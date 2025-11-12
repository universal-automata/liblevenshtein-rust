use liblevenshtein::transducer::transition::{initial_state, transition_state};
use liblevenshtein::transducer::{Algorithm, Unrestricted};

#[test]
fn test_transition_debug() {
    let query = b"test";
    let max_distance = 0;

    // Initial state
    let state = initial_state(query.len(), max_distance, Algorithm::Standard);
    println!("Initial state positions: {:?}", state.positions());

    // Try transitioning with 't'
    let next = transition_state(
        &state,
        Unrestricted,
        b't',
        query,
        max_distance,
        Algorithm::Standard,
        false,
    );
    println!(
        "After 't' transition: {:?}",
        next.as_ref().map(|s| s.positions())
    );

    if let Some(next_state) = next {
        // Try transitioning with 'e'
        let next2 = transition_state(
            &next_state,
            Unrestricted,
            b'e',
            query,
            max_distance,
            Algorithm::Standard,
            false,
        );
        println!(
            "After 'e' transition: {:?}",
            next2.as_ref().map(|s| s.positions())
        );

        if let Some(next_state2) = next2 {
            // Try transitioning with 's'
            let next3 = transition_state(
                &next_state2,
                Unrestricted,
                b's',
                query,
                max_distance,
                Algorithm::Standard,
                false,
            );
            println!(
                "After 's' transition: {:?}",
                next3.as_ref().map(|s| s.positions())
            );

            if let Some(next_state3) = next3 {
                // Try transitioning with final 't'
                let next4 = transition_state(
                    &next_state3,
                    Unrestricted,
                    b't',
                    query,
                    max_distance,
                    Algorithm::Standard,
                    false,
                );
                println!(
                    "After final 't' transition: {:?}",
                    next4.as_ref().map(|s| s.positions())
                );

                if let Some(final_state) = next4 {
                    println!(
                        "Final state inferred distance: {:?}",
                        final_state.infer_distance(query.len())
                    );
                }
            }
        }
    }
}
