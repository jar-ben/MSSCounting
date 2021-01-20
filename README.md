# MSSCounter
Given an unsatisfiable set F = {f1, ..., fn} of Boolean clauses, i.e., a Boolean formula in CNF, this tool counts the number of Maximal Satisfiable Subsets (MSS) of F. 
In particular, a subset N of F is an MSS of F iff N is satisfiable and every proper supserset of N (w.r.t. F) is unsatisfiable. Note that the maximality here is the set maximality and not the maximum cardinality as in the MaxSAT problem. Consequently, there can be up to 2^|F| many MSSes of F (this is the maximum number of pair-wise incomparable subsets of F). 
This tool also counts the number of Minimal Correction Subsets (MCSes) of F, where a subset N of F is an MCS iff F\N is satisfiable and for every proper subset N' of N, the set F\N' is unsatisfiable. Note that the MCSes of F are exactly the complements of MSSes of F, hence, the number of MSSes and MCSes of F is the same. 

# Related Tools


# Citation
A paper that introduces our counting approach was accepted to AAAI 2021 (to appear). If you use the tool, please, cite our paper:
"Counting Maximal Satisfiable Subsets" by Jaroslav Bendik, and Kuldeep S. Meel. 
