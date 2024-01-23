# legogro16

This crate contains an implementation of the LegoGro16 zkSNARK based on https://github.com/kobigurk/legogro16, but rewritten using Arkworks version v0.4.0.

NOTE1: We assume here that all witnesses (private input) are included in the proof.d commitment. 

NOTE2: code contains two approaches, one CP-link and one with only the proof.d commitment. 
