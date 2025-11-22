# Resource Limiting for Coq/Rocq Compilation

## Problem
Rocq worker processes can consume excessive system resources (memory, CPU, disk IO), making the system unresponsive during proof compilation.

## Solution
Use `systemd-run` with cgroups v2 resource controls to limit resource usage.

---

## Recommended Command

### Standard Build (150GB RAM, 27 cores, -j4 parallel jobs)
```bash
systemd-run --user --scope \
  -p MemoryMax=150G \
  -p CPUQuota=2700% \
  -p IOWeight=50 \
  -p TasksMax=300 \
  make -j4
```

**Parameters Explained:**
- `--user`: Run in user session (no sudo required)
- `--scope`: Run synchronously (see output directly)
- `-p MemoryMax=150G`: Hard limit of 150GB RAM (~60% of 252GB)
- `-p CPUQuota=2700%`: Limit to 27 cores (75% of 36 cores; 100% = 1 core in systemd)
- `-p IOWeight=50`: Lower IO priority to reduce disk thrashing
- `-p TasksMax=300`: Limit total number of processes/threads
- `make -j4`: Run 4 parallel compilation jobs

**Important: Understanding `-j` vs `CPUQuota`:**
- **`-j4`**: Controls how many **make targets** (files) compile simultaneously
- **`CPUQuota=2700%`**: Controls **total CPU resources** available (27 cores)
- Each Coq/Rocq compilation can spawn multiple worker threads internally
- With `-j4` and 27 cores: each job gets ~6-7 cores on average
- **Don't set `-j` equal to CPU cores!** Each job needs multiple cores for internal parallelism
- Recommended: `-j4` to `-j8` for optimal memory/CPU balance (each job may use 10-20GB RAM)

---

## Choosing the Right `-j` Value

**Rule of thumb**: Set `-j` to **10-25% of available CPU cores**, not equal to cores.

| CPU Cores | CPUQuota | Recommended `-j` | Reasoning |
|-----------|----------|------------------|-----------|
| 36 cores  | 2700% (27 cores) | `-j4` to `-j8` | Each job gets 3-7 cores for internal workers |
| 24 cores  | 1800% (18 cores) | `-j3` to `-j6` | Balanced parallelism |
| 16 cores  | 1200% (12 cores) | `-j2` to `-j4` | Prevents memory exhaustion |
| 8 cores   | 600% (6 cores)   | `-j2` | Single file compilation may use 3 cores |

**Why not `-j27` with 27 cores?**
- Each Coq file compilation is memory-intensive (10-20GB per file)
- Running 27 files in parallel would require ~270-540GB RAM (exceeds our 150GB limit)
- Coq internally spawns worker processes that benefit from multiple cores per job
- Dependencies between files mean many jobs would be blocked waiting anyway

**Experimentation**:
- Start with `-j4`, monitor with `htop`
- If CPU usage is low (<50%) and memory is fine, try `-j6` or `-j8`
- If memory pressure or system sluggishness, reduce to `-j2` or `-j3`

---

## Alternative Configurations

### Conservative (100GB RAM, 18 cores, -j2)
Use if system still feels sluggish:
```bash
systemd-run --user --scope \
  -p MemoryMax=100G \
  -p CPUQuota=1800% \
  -p IOWeight=30 \
  -p TasksMax=200 \
  make -j2
```

### Aggressive (200GB RAM, 32 cores, -j8)
Use if you want faster builds and can tolerate some system slowdown:
```bash
systemd-run --user --scope \
  -p MemoryMax=200G \
  -p CPUQuota=3200% \
  -p IOWeight=100 \
  -p TasksMax=500 \
  make -j8
```

### Single-threaded (for debugging)
When you need to see errors clearly without parallel compilation:
```bash
systemd-run --user --scope \
  -p MemoryMax=100G \
  -p CPUQuota=900% \
  -p IOWeight=30 \
  make -j1
```

---

## Usage in This Project

### Full Build
```bash
cd /home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/docs/verification/phonetic

# Clean and rebuild everything
systemd-run --user --scope \
  -p MemoryMax=150G \
  -p CPUQuota=2700% \
  -p IOWeight=50 \
  -p TasksMax=300 \
  bash -c "make clean && make -j4 2>&1 | tee /tmp/coq_build.log"
```

### Compile Specific Module
```bash
systemd-run --user --scope \
  -p MemoryMax=150G \
  -p CPUQuota=2700% \
  -p IOWeight=50 \
  -p TasksMax=300 \
  make theories/Patterns/PatternOverlap.vo
```

---

## Monitoring During Compilation

### Check resource usage in real-time
```bash
# Watch memory and CPU of rocq processes
watch -n 2 'ps aux | grep -E "rocq|coq" | grep -v grep'

# Or use htop filtered to rocq processes
htop -p $(pgrep -d',' rocq)
```

### Check systemd cgroup limits
```bash
# Show resource usage of the running scope
systemctl --user status run-*.scope

# Show detailed cgroup statistics
systemd-cgtop --user
```

---

## Emergency Kill Switch

If the system becomes unresponsive despite limits:

```bash
# Kill all rocq/coq processes
pkill -9 rocq
pkill -9 coq
pkill -9 make

# Or kill the systemd scope
systemctl --user stop run-*.scope

# Or kill all user processes in the cgroup
systemctl --user kill run-*.scope
```

---

## Why These Limits Work

### Memory Limit (MemoryMax)
- Prevents OOM (Out of Memory) killer from terminating other processes
- If rocqworker exceeds 150GB, it will be killed instead of your desktop/browser
- systemd enforces this at the cgroup level (kernel-level protection)

### CPU Quota (CPUQuota)
- Ensures other processes can still run (desktop, browser, etc.)
- 2700% = 27 cores out of 36 (75% utilization)
- Remaining 9 cores available for OS and other applications

### IO Weight (IOWeight)
- Reduces disk IO priority for Coq compilation
- Prevents compilation from causing disk thrashing
- Lower values (30-50) = less aggressive disk usage

### TasksMax
- Limits total number of processes/threads spawned
- Prevents fork bombs if something goes wrong
- 300 tasks should be sufficient for parallel compilation

---

## System Specifications (for reference)

- **CPU**: Intel Xeon E5-2699 v3 (36 physical cores, 72 threads)
- **RAM**: 252 GB DDR4 ECC
- **OS**: Arch Linux (kernel 6.17.8)
- **Coq/Rocq**: Rocq Prover 9.1.0

---

## Notes

1. **No sudo required**: `systemd-run --user` works without root privileges
2. **cgroups v2**: Arch Linux uses cgroups v2 by default (required for these features)
3. **Log files**: Always use `tee` to capture output to a log file for debugging
4. **Exit code 137**: Means the process was killed by OOM (memory limit exceeded)
5. **Adjust as needed**: Monitor your system and adjust limits based on responsiveness

---

## Troubleshooting

### "Failed to create bus connection"
```bash
# Check if systemd user session is running
systemctl --user status

# If not running, start it
systemctl --user start
```

### Memory limit too restrictive (exit code 137)
Increase MemoryMax:
```bash
systemd-run --user --scope -p MemoryMax=200G -p CPUQuota=2700% -p IOWeight=50 make -j4
```

### Compilation too slow
Increase CPUQuota and parallel jobs:
```bash
systemd-run --user --scope -p MemoryMax=150G -p CPUQuota=3200% -p IOWeight=100 make -j8
```

---

## Quick Reference

**Command used for successful compilation (2025-11-20)**:
```bash
systemd-run --user --scope \
  -p MemoryMax=150G \
  -p CPUQuota=2700% \
  -p IOWeight=50 \
  -p TasksMax=300 \
  make -j4 2>&1 | tee /tmp/compile_j4_limited.log
```

This configuration successfully compiled all 9 Coq modules without system unresponsiveness.
