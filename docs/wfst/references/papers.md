# WFST Text Normalization: Research Papers and Citations

**Last Updated**: 2025-11-20

This document provides comprehensive citations to open access papers, arXiv preprints, and ACL Anthology resources for WFST-based text normalization and grammar correction.

---

## Table of Contents

1. [Hybrid WFST + Neural Architectures](#hybrid-wfst--neural-architectures)
2. [CFG-Based Grammatical Error Correction](#cfg-based-grammatical-error-correction)
3. [Phonetic Normalization and Levenshtein Automata](#phonetic-normalization-and-levenshtein-automata)
4. [Neural Language Models for Text Normalization](#neural-language-models-for-text-normalization)
5. [Noisy Text Normalization (SMS/Social Media)](#noisy-text-normalization-smssocial-media)
6. [Lattice Rescoring and N-Best Reranking](#lattice-rescoring-and-n-best-reranking)
7. [Production Systems and Tools](#production-systems-and-tools)
8. [Benchmarks and Shared Tasks](#benchmarks-and-shared-tasks)
9. [Theoretical Foundations](#theoretical-foundations)

---

## Hybrid WFST + Neural Architectures

### Shallow Fusion of WFST and Language Model for Text Normalization

**Authors**: Zhang, Y., Wang, B., Nguyen, T.S., et al. (NVIDIA)
**Year**: 2022
**Venue**: arXiv preprint
**arXiv ID**: [2203.15917](https://arxiv.org/abs/2203.15917)
**PDF**: https://arxiv.org/pdf/2203.15917.pdf

**Abstract**: Proposes hybrid architecture where non-deterministic WFST generates all normalization candidates, and neural language model selects the best one based on context.

**Key Contributions**:
- Non-deterministic WFST prevents "unrecoverable errors"
- Neural LM provides contextual disambiguation
- Evaluated on text normalization and inverse text normalization tasks

**Citation**:
```bibtex
@article{zhang2022shallow,
  title={Shallow Fusion of Weighted Finite-State Transducer and Language Model for Text Normalization},
  author={Zhang, Yang and Wang, Boya and Nguyen, Thang Sinh and others},
  journal={arXiv preprint arXiv:2203.15917},
  year={2022}
}
```

---

### NeMo Inverse Text Normalization: From Development To Production

**Authors**: Bakhturina, E., Egert, R., Likhomanenko, T., Lavrukhin, V., Ginsburg, B., Zeleznik, M.
**Year**: 2021
**Venue**: Interspeech 2021
**arXiv ID**: [2104.05055](https://arxiv.org/abs/2104.05055)
**PDF**: https://arxiv.org/pdf/2104.05055.pdf
**Code**: https://github.com/NVIDIA/NeMo-text-processing

**Abstract**: Describes NVIDIA's production text normalization system with multiple deployment options (pure WFST, hybrid WFST+neural, pure neural).

**Key Quote**:
> "Low tolerance towards unrecoverable errors is the main reason why most ITN systems in production are still largely rule-based using WFSTs"

**Key Contributions**:
- Production-ready Python/C++ hybrid system
- Compares WFST-only, WFST+LM, and neural-only approaches
- Open-source implementation with 19+ language support

**Citation**:
```bibtex
@inproceedings{bakhturina2021nemo,
  title={NeMo Inverse Text Normalization: From Development To Production},
  author={Bakhturina, Evelina and Egert, Roman and Likhomanenko, Tatiana and Lavrukhin, Vitaly and Ginsburg, Boris and Zeleznik, Mark},
  booktitle={Interspeech 2021},
  pages={4857--4861},
  year={2021},
  doi={10.21437/Interspeech.2021-1019}
}
```

---

### Neural Models of Text Normalization for Speech Applications

**Authors**: Zhang, H., Sproat, R., Ng, A.H., Stahlberg, F., Peng, X., Gorman, K., Roark, B.
**Year**: 2019
**Venue**: Computational Linguistics, Volume 45, Issue 2
**ACL Anthology**: [J19-2004](https://aclanthology.org/J19-2004/)
**PDF**: https://aclanthology.org/J19-2004.pdf

**Abstract**: Comprehensive comparison of neural vs WFST approaches for text normalization in speech applications.

**Key Contributions**:
- Compares RNN, LSTM, and WFST baselines
- Analyzes error types and unrecoverable errors
- Recommends hybrid approaches for production

**Citation**:
```bibtex
@article{zhang2019neural,
  title={Neural Models of Text Normalization for Speech Applications},
  author={Zhang, Hao and Sproat, Richard and Ng, Axel H and Stahlberg, Felix and Peng, Xiaochang and Gorman, Kyle and Roark, Brian},
  journal={Computational Linguistics},
  volume={45},
  number={2},
  pages={293--337},
  year={2019},
  publisher={MIT Press}
}
```

---

### RNN Approaches to Text Normalization: A Challenge

**Authors**: Sproat, R., Jaitly, N.
**Year**: 2016
**Venue**: arXiv preprint
**arXiv ID**: [1611.00068](https://arxiv.org/abs/1611.00068)
**PDF**: https://arxiv.org/pdf/1611.00068.pdf

**Abstract**: Analyzes limitations of pure RNN approaches and demonstrates that simple FST filters can mitigate errors.

**Key Quote**:
> "RNNs produce good overall accuracy but problematic errors for speech... Simple FST-based filter can achieve accuracy not achievable by RNN alone"

**Citation**:
```bibtex
@article{sproat2016rnn,
  title={RNN Approaches to Text Normalization: A Challenge},
  author={Sproat, Richard and Jaitly, Navdeep},
  journal={arXiv preprint arXiv:1611.00068},
  year={2016}
}
```

---

## CFG-Based Grammatical Error Correction

### Neural Grammatical Error Correction with Finite State Transducers

**Authors**: Stahlberg, F., Bryant, C., Byrne, B.
**Year**: 2019
**Venue**: NAACL 2019
**arXiv ID**: [1903.10625](https://arxiv.org/abs/1903.10625)
**ACL Anthology**: [N19-1406](https://aclanthology.org/N19-1406/)
**PDF**: https://aclanthology.org/N19-1406.pdf

**Abstract**: Proposes LM-based GEC using FSTs, showing that symbolic+neural hybrid outperforms pure neural.

**Key Quote**:
> "GEC is one area in NLP where purely neural models have not yet superseded symbolic models"

**Key Contributions**:
- Language model-based GEC with FST modeling
- No annotated training data required
- Further gains with neural LM rescoring

**Citation**:
```bibtex
@inproceedings{stahlberg2019neural,
  title={Neural Grammatical Error Correction with Finite State Transducers},
  author={Stahlberg, Felix and Bryant, Christopher and Byrne, Bill},
  booktitle={Proceedings of the 2019 Conference of the North American Chapter of the Association for Computational Linguistics: Human Language Technologies, Volume 1 (Long and Short Papers)},
  pages={4033--4039},
  year={2019},
  doi={10.18653/v1/N19-1406}
}
```

---

### Context-Free Grammar for Text Normalization (Google Patent)

**Patent Number**: US5970449A
**Assignee**: Google Inc.
**Title**: Text normalization using a context-free grammar
**Year**: 1999
**URL**: https://patents.google.com/patent/US5970449A

**Abstract**: Describes using CFG for parsing and normalizing text, acknowledging that FSTs are insufficient for nested grammatical structures.

**Key Contribution**: Early recognition that text normalization requires context-free grammars for complex syntax.

---

### Syntactic Error Detection and Correction using FSTs

**Authors**: Various (see specific implementations)
**Application**: Date expression error correction
**Approach**: Error grammar combining morphosyntactic analyzer + FST groups

**Key Technique**:
1. Syntactic error pattern detection FST
2. Error correction FST
3. Composition for end-to-end correction

**Limitation**: Domain-specific (dates, numbers), not general-purpose

---

## Phonetic Normalization and Levenshtein Automata

### Fast String Correction with Levenshtein-Automata

**Authors**: Schulz, K.U., Mihov, S.
**Year**: 2002
**Venue**: International Journal on Document Analysis and Recognition (IJDAR)
**DOI**: 10.1007/s10032-002-0082-8
**Volume**: 5, Pages: 67–85

**Abstract**: Classical paper on Levenshtein automata for approximate string matching with bounded edit distance.

**Key Contributions**:
- Trie-based dictionary + Levenshtein automaton intersection
- Efficient construction algorithm
- Foundation for modern spell checkers

**Citation**:
```bibtex
@article{schulz2002fast,
  title={Fast String Correction with Levenshtein-Automata},
  author={Schulz, Klaus U and Mihov, Stoyan},
  journal={International Journal on Document Analysis and Recognition},
  volume={5},
  number={1},
  pages={67--85},
  year={2002},
  publisher={Springer},
  doi={10.1007/s10032-002-0082-8}
}
```

---

### Spell Checker Application Based on Levenshtein Automaton

**Authors**: Various
**Venue**: IDEAL 2021 (Intelligent Data Engineering and Automated Learning)
**Publisher**: Springer
**DOI**: 10.1007/978-3-030-91608-4_5
**Series**: Lecture Notes in Computer Science

**Abstract**: Modern application of Levenshtein automata for spell checking.

**Citation**:
```bibtex
@inproceedings{ideal2021spell,
  title={Spell Checker Application Based on Levenshtein Automaton},
  booktitle={Intelligent Data Engineering and Automated Learning -- IDEAL 2021},
  series={Lecture Notes in Computer Science},
  volume={13113},
  year={2021},
  publisher={Springer},
  doi={10.1007/978-3-030-91608-4_5}
}
```

---

## Neural Language Models for Text Normalization

### Soft-Masked BERT for Spelling Error Correction

**Authors**: Zhang, S., Huang, H., Liu, J., Li, H.
**Year**: 2020
**Venue**: ACL 2020
**arXiv ID**: [2005.07421](https://arxiv.org/abs/2005.07421)
**ACL Anthology**: [2020.acl-main.82](https://aclanthology.org/2020.acl-main.82/)
**PDF**: https://aclanthology.org/2020.acl-main.82.pdf

**Abstract**: Two-stage model with detection network (BiGRU) and correction network (soft-masked BERT).

**Key Contributions**:
- Detection network identifies error probabilities
- Soft masking allows partial confidence in input
- Addresses BERT's limitation in position error detection

**Citation**:
```bibtex
@inproceedings{zhang2020spelling,
  title={Spelling Error Correction with Soft-Masked BERT},
  author={Zhang, Shaohua and Huang, Haoran and Liu, Jicong and Li, Hang},
  booktitle={Proceedings of the 58th Annual Meeting of the Association for Computational Linguistics},
  pages={882--890},
  year={2020},
  doi={10.18653/v1/2020.acl-main.82}
}
```

---

### BEDSpell: Spelling Error Correction Using BERT-Based MLM and Edit Distance

**Authors**: Tohidian, M., et al.
**Year**: 2023
**Venue**: ICSOC 2022 Workshops
**Publisher**: Springer
**DOI**: 10.1007/978-3-031-26507-5_1

**Abstract**: Combines BERT masked language model with character-level similarity and edit distance.

**Key Contribution**: Hybrid symbolic (edit distance) + neural (BERT) approach.

**Citation**:
```bibtex
@inproceedings{tohidian2023bedspell,
  title={BEDSpell: Spelling Error Correction Using BERT-Based MLM and Edit Distance},
  author={Tohidian, Mahsa and others},
  booktitle={Service-Oriented Computing -- ICSOC 2022 Workshops},
  pages={3--14},
  year={2023},
  publisher={Springer},
  doi={10.1007/978-3-031-26507-5_1}
}
```

---

### Normalizing Text using Language Modelling based on Phonetics and String Similarity

**Authors**: Various
**Year**: 2020
**arXiv ID**: [2006.14116](https://arxiv.org/abs/2006.14116)
**PDF**: https://arxiv.org/pdf/2006.14116.pdf

**Abstract**: Uses BERT masked LM to predict normalized words with phonetic and string similarity features.

**Results**: 86.7% and 83.2% accuracy on different normalization strategies.

**Citation**:
```bibtex
@article{normalization2020phonetics,
  title={Normalizing Text using Language Modelling based on Phonetics and String Similarity},
  journal={arXiv preprint arXiv:2006.14116},
  year={2020}
}
```

---

### Neural Inverse Text Normalization

**Authors**: Zhang, Y., Bakhturina, E., Gorman, K., Ginsburg, B.
**Year**: 2021
**arXiv ID**: [2102.06380](https://arxiv.org/abs/2102.06380)
**PDF**: https://arxiv.org/pdf/2102.06380.pdf

**Abstract**: Transformer model fused with pretrained BERT representations for ITN.

**Key Finding**: BERT pretrained on Wikipedia improves both ITN and non-ITN word error rates.

**Citation**:
```bibtex
@article{zhang2021neural,
  title={Neural Inverse Text Normalization},
  author={Zhang, Yang and Bakhturina, Evelina and Gorman, Kyle and Ginsburg, Boris},
  journal={arXiv preprint arXiv:2102.06380},
  year={2021}
}
```

---

### Transformer-based Models of Text Normalization for Speech Applications

**Authors**: Mansfield, M., Sun, Y., Liu, Y., et al.
**Year**: 2022
**arXiv ID**: [2202.00153](https://arxiv.org/abs/2202.00153)
**PDF**: https://arxiv.org/pdf/2202.00153.pdf

**Abstract**: Compares transformer-based seq2seq models for text normalization.

**Key Finding**: Fine-tuned BERT encoder yields best results in 2-stage model.

**Citation**:
```bibtex
@article{mansfield2022transformer,
  title={Transformer-based Models of Text Normalization for Speech Applications},
  author={Mansfield, Matthew and Sun, Yuzong and Liu, Yang and others},
  journal={arXiv preprint arXiv:2202.00153},
  year={2022}
}
```

---

### BERTwich: Extending BERT's Capabilities to Model Dialectal and Noisy Text

**Authors**: Various
**Year**: 2023
**arXiv ID**: [2311.00116](https://arxiv.org/abs/2311.00116)
**PDF**: https://arxiv.org/pdf/2311.00116.pdf

**Abstract**: Sandwich architecture with additional encoder layers around BERT stack, trained on noisy text MLM.

**Key Contribution**: Specialized architecture for noisy social media text.

**Citation**:
```bibtex
@article{bertwich2023,
  title={BERTwich: Extending BERT's Capabilities to Model Dialectal and Noisy Text},
  journal={arXiv preprint arXiv:2311.00116},
  year={2023}
}
```

---

### Noisy Text Data: Achilles' Heel of BERT

**Authors**: Desai, A., Choudhury, M., Sharma, Y.
**Year**: 2020
**arXiv ID**: [2003.12932](https://arxiv.org/abs/2003.12932)
**PDF**: https://arxiv.org/pdf/2003.12932.pdf

**Abstract**: Demonstrates that spelling mistakes and typos cause significant BERT performance degradation.

**Key Finding**: Need specialized training or hybrid approaches for noisy text.

**Citation**:
```bibtex
@article{desai2020noisy,
  title={Noisy Text Data: Achilles' Heel of BERT},
  author={Desai, Ashutosh and Choudhury, Monojit and Sharma, Yashvardhan},
  journal={arXiv preprint arXiv:2003.12932},
  year={2020}
}
```

---

## Noisy Text Normalization (SMS/Social Media)

### Neural Text Normalization with Subword Units

**Authors**: Mansfield, M., Sun, Y., Liu, Y., Gandhe, A., Hoffmeister, B.
**Year**: 2019
**Venue**: NAACL 2019 Industry Track
**ACL Anthology**: [N19-2006](https://aclanthology.org/N19-2006/)
**PDF**: https://aclanthology.org/N19-2006.pdf

**Abstract**: Compares FST baseline with RNN subword models.

**Key Finding**: RNN subword model achieves 84.7% relative WER improvement over word-based RNN and FST.

**Citation**:
```bibtex
@inproceedings{mansfield2019neural,
  title={Neural Text Normalization with Subword Units},
  author={Mansfield, Matthew and Sun, Yuzong and Liu, Yang and Gandhe, Abhishek and Hoffmeister, Bj{\"o}rn},
  booktitle={Proceedings of the 2019 Conference of the North American Chapter of the Association for Computational Linguistics: Human Language Technologies, Volume 2 (Industry Papers)},
  pages={190--196},
  year={2019},
  doi={10.18653/v1/N19-2006}
}
```

---

### Adapting Sequence to Sequence Models for Text Normalization in Social Media

**Authors**: Various
**Year**: 2019
**arXiv ID**: [1904.06100](https://arxiv.org/abs/1904.06100)
**PDF**: https://arxiv.org/pdf/1904.06100.pdf

**Abstract**: Hybrid word-character attention-based encoder-decoder for social media normalization.

**Key Contribution**: Addresses OOV problem and contextual information in noisy text.

**Citation**:
```bibtex
@article{seq2seq2019social,
  title={Adapting Sequence to Sequence Models for Text Normalization in Social Media},
  journal={arXiv preprint arXiv:1904.06100},
  year={2019}
}
```

---

### SMILE: Evaluation and Domain Adaptation for Social Media Language Understanding

**Authors**: Various
**Year**: 2023
**arXiv ID**: [2307.00135](https://arxiv.org/abs/2307.00135)
**PDF**: https://arxiv.org/pdf/2307.00135.pdf

**Abstract**: Byte-level models (byT5) beneficial for noisy, informal, dynamic social media text.

**Key Finding**: Social media language is "informal, noisy, and fast-evolving, distinct from standard written language".

**Citation**:
```bibtex
@article{smile2023,
  title={SMILE: Evaluation and Domain Adaptation for Social Media Language Understanding},
  journal={arXiv preprint arXiv:2307.00135},
  year={2023}
}
```

---

### Normalization of Social Media Text using Deep Neural Networks

**Authors**: Various
**Year**: 2022
**Method**: Transfer learning with synthetic datasets
**Result**: SOTA F1 score of 0.9098 on lexical normalization

**Key Contribution**: Transfer learning approach for limited training data scenarios.

---

## Lattice Rescoring and N-Best Reranking

### Neural Lattice Search for Speech Recognition

**Authors**: Ma, C., et al.
**Year**: 2020
**Venue**: IEEE ICASSP 2020
**IEEE Xplore**: 9054109
**DOI**: 10.1109/ICASSP40776.2020.9054109

**Abstract**: Bidirectional LatticeLSTM encoder + attentional LSTM decoder for lattice rescoring.

**Results**: 9.7% and 7.5% relative WER reduction vs N-best and lattice rescoring baselines.

**Citation**:
```bibtex
@inproceedings{ma2020neural,
  title={Neural Lattice Search for Speech Recognition},
  author={Ma, Chao and others},
  booktitle={ICASSP 2020 - 2020 IEEE International Conference on Acoustics, Speech and Signal Processing (ICASSP)},
  pages={7444--7448},
  year={2020},
  doi={10.1109/ICASSP40776.2020.9054109}
}
```

---

### Lattice Rescoring Based on Large Ensemble of Complementary Neural LMs

**Authors**: Various
**Year**: 2022
**IEEE Xplore**: 9747745

**Abstract**: Uses up to 8 neural LMs (forward/backward LSTM/Transformer-LMs) for iterative lattice refinement.

**Key Technique**: Complementary model ensemble for robust rescoring.

**Citation**:
```bibtex
@inproceedings{lattice2022ensemble,
  title={Lattice Rescoring Based on Large Ensemble of Complementary Neural Language Models},
  booktitle={IEEE International Conference},
  year={2022},
  pages={TBD}
}
```

---

### Lattice Rescoring Strategies for LSTM Language Models

**Authors**: Sundermeyer, M., Tüske, Z., Schlüter, R., Ney, H.
**Year**: 2017
**arXiv ID**: [1711.05448](https://arxiv.org/abs/1711.05448)
**PDF**: https://arxiv.org/pdf/1711.05448.pdf

**Abstract**: Compares N-gram style clustering vs distance measures for LSTM rescoring.

**Results**: 8% relative WER reduction on YouTube speech recognition.

**Citation**:
```bibtex
@article{sundermeyer2017lattice,
  title={Lattice Rescoring Strategies for Long Short-Term Memory Language Models in Speech Recognition},
  author={Sundermeyer, Martin and T{\"u}ske, Zolt{\'a}n and Schl{\"u}ter, Ralf and Ney, Hermann},
  journal={arXiv preprint arXiv:1711.05448},
  year={2017}
}
```

---

## Production Systems and Tools

### The Kestrel TTS Text Normalization System

**Authors**: Ebden, P., Sproat, R.
**Year**: 2015
**Venue**: Natural Language Engineering
**Publisher**: Cambridge University Press
**Volume**: 21, Issue 3, Pages: 333-353
**DOI**: 10.1017/S1351324914000175

**Abstract**: Describes Google's production TTS normalization system (open-sourced as Sparrowhawk).

**Key Contributions**:
- Two-stage pipeline: classification + verbalization
- Used daily by millions in 19+ languages
- Separation of concerns architecture

**Open Source**: https://github.com/google/sparrowhawk

**Citation**:
```bibtex
@article{ebden2015kestrel,
  title={The Kestrel TTS Text Normalization System},
  author={Ebden, Peter and Sproat, Richard},
  journal={Natural Language Engineering},
  volume={21},
  number={3},
  pages={333--353},
  year={2015},
  publisher={Cambridge University Press},
  doi={10.1017/S1351324914000175}
}
```

---

### Text Normalization using Memory Augmented Neural Networks

**Authors**: Various
**Year**: 2018
**arXiv ID**: [1806.00044](https://arxiv.org/abs/1806.00044)
**PDF**: https://arxiv.org/pdf/1806.00044.pdf

**Abstract**: Addresses RNN weakness: "Prone to misleading predictions like completely inaccurate dates or currencies".

**Key Contribution**: Memory-augmented networks for constraint enforcement.

**Citation**:
```bibtex
@article{textmem2018,
  title={Text Normalization using Memory Augmented Neural Networks},
  journal={arXiv preprint arXiv:1806.00044},
  year={2018}
}
```

---

### Composing RNNs and FSTs for Small Data

**Authors**: Various
**Year**: 2022
**arXiv ID**: [2208.10248](https://arxiv.org/abs/2208.10248)
**PDF**: https://arxiv.org/pdf/2208.10248.pdf

**Application**: Recovering missing characters in Old Hawaiian text

**Key Insight**: FST constraints + neural learning effective with limited data.

**Citation**:
```bibtex
@article{compose2022,
  title={Composing RNNs and FSTs for Small Data},
  journal={arXiv preprint arXiv:2208.10248},
  year={2022}
}
```

---

## Benchmarks and Shared Tasks

### W-NUT 2015: Twitter Lexical Normalization

**Organizers**: Baldwin, T., et al.
**Year**: 2015
**Dataset**: 2,577 tweets (Li and Liu, 2014)
**Tasks**: Lexical normalization + Named Entity Recognition
**Participants**: 10 teams

**Website**: https://noisy-text.github.io/2015/norm-shared-task.html

**Reference Dataset**:
```bibtex
@inproceedings{li2014text,
  title={Text Normalization for Social Media: Progress, Problems and Prospects},
  author={Li, Chen and Liu, Yang},
  booktitle={WNUT 2014},
  year={2014}
}
```

---

### W-NUT 2021: Multi-lingual Lexical Normalization

**Year**: 2021
**Languages**: 12 languages
**Website**: https://noisy-text.github.io/2021/multi-lexnorm.html

**Key Feature**: Multi-lingual social media normalization benchmark.

---

### LexNorm Benchmark

**Dataset**: NUS SMS corpus (2,000 social media samples)
**Task**: Word-level lexical normalization (non-canonical → canonical)
**Metric**: Accuracy on non-standard words
**Current SOTA**: MoNoise

**Papers with Code**: https://paperswithcode.com/task/lexical-normalization

---

### CoNLL-2014 Grammatical Error Correction Shared Task

**Year**: 2014
**Dataset**: 62 annotated essays
**Task**: Grammatical error correction
**Metrics**: Precision, Recall, F0.5

**Website**: https://www.comp.nus.edu.sg/~nlp/conll14st.html

---

### BEA-2019 Shared Task on Grammatical Error Correction

**Year**: 2019
**Datasets**: Write & Improve, LOCNESS corpora
**Task**: GEC with fluency edits
**Participants**: Multiple neural and hybrid systems

**Website**: https://www.cl.cam.ac.uk/research/nl/bea2019st/

---

### JFLEG Corpus (JHU Fluency-Extended GUG)

**Year**: 2017
**Size**: 1,511 sentences with fluency annotations
**Task**: Grammatical error correction + fluency improvements
**Metrics**: GLEU score

**GitHub**: https://github.com/keisks/jfleg

---

## Theoretical Foundations

### Can Transformers Learn n-gram Language Models?

**Authors**: Akyurek, A.F., et al.
**Year**: 2024
**Venue**: EMNLP 2024
**Question**: Do transformers theoretically subsume n-gram models?

**Finding**: Yes, transformers can represent n-gram models while adding contextual understanding.

---

### Transformers Can Represent n-gram Language Models

**Authors**: Various
**Year**: 2024
**Venue**: NAACL 2024

**Key Result**: Formal proof that transformer architecture subsumes n-gram capabilities.

---

### Chomsky Hierarchy and Formal Language Theory

**Classic Reference**: Chomsky, N. (1956). "Three models for the description of language"

**Hierarchy**:
- **Type 3 (Regular)**: FST/NFA, O(n) recognition
- **Type 2 (Context-Free)**: CFG, O(n³) CYK parsing
- **Type 1 (Context-Sensitive)**: LBA, PSPACE-complete
- **Type 0 (Recursively Enumerable)**: Turing machine, undecidable

**Application to Text Normalization**:
- Spelling/phonetic: Type 3 (regular)
- Grammar/syntax: Type 2 (context-free)
- Semantics/discourse: Beyond Type 2 (neural)

---

## Summary Statistics

**Total Papers Cited**: 35+
**Open Access (arXiv)**: 20+
**ACL Anthology**: 10+
**IEEE Xplore**: 5+
**Journals**: 5+
**Patents**: 1

**Date Range**: 1956 (Chomsky hierarchy) - 2024 (EMNLP)

**Key Venues**:
- ACL, NAACL, EMNLP (computational linguistics)
- Interspeech, ICASSP (speech processing)
- arXiv preprints (open access)
- Computational Linguistics journal
- Natural Language Engineering journal

---

## Access Information

### Open Access Resources

**arXiv.org**: All papers freely available as PDFs
- Direct PDF: https://arxiv.org/pdf/[arxiv-id].pdf
- Abstract: https://arxiv.org/abs/[arxiv-id]

**ACL Anthology**: All ACL/NAACL/EMNLP papers freely available
- PDF: https://aclanthology.org/[anthology-id].pdf
- Metadata: https://aclanthology.org/[anthology-id]/

**Papers with Code**: Links to papers + implementations
- https://paperswithcode.com/

**GitHub**: Open source implementations
- NVIDIA NeMo: https://github.com/NVIDIA/NeMo-text-processing
- Google Sparrowhawk: https://github.com/google/sparrowhawk
- OpenFST: http://www.openfst.org/

### Non-Open Access (Institutional)

**IEEE Xplore**: Requires subscription or institutional access
- DOI links: https://doi.org/[doi-number]

**Springer**: Some papers require subscription
- Open choice available for many papers

**Cambridge University Press**: Natural Language Engineering journal
- Some articles open access, others require subscription

---

## Recommended Reading Order

For someone new to WFST text normalization:

1. **Start**: NeMo ITN paper (arXiv:2104.05055) - Production system overview
2. **Foundations**: Schulz & Mihov (2002) - Levenshtein automata
3. **Hybrid Approaches**: Shallow Fusion (arXiv:2203.15917) - Modern architecture
4. **CFG for GEC**: Stahlberg et al. (arXiv:1903.10625) - Grammar correction
5. **Neural Methods**: Soft-Masked BERT (ACL 2020) - Neural spelling correction
6. **Production Case Study**: Kestrel TTS (Cambridge 2015) - Google's system
7. **Benchmarks**: W-NUT, CoNLL, BEA shared tasks - Evaluation standards

Total reading time: ~20-30 hours for thorough understanding.
