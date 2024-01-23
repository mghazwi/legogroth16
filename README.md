# legogro16

This crate contains an implementation of the LegoGro16 zkSNARK based on https://github.com/kobigurk/legogro16, but rewritten using Arkworks version v0.4.0.

NOTE 1: We assume here that all input (both public and private) are assigned as witnesses and included in the proof.d commitment.  

NOTE 2: Does making CP-link optional reduce the security? We don't need the link, only the commitment to the witness is needed in the proof (inside proof.d).