# MSSCounter
Given an unsatisfiable set F = {f1, ..., fn} of Boolean clauses, i.e., a Boolean formula in CNF, this tool counts the number of Maximal Satisfiable Subsets (MSS) of F. 
In particular, a subset N of F is an MSS of F iff N is satisfiable and every proper supserset of N (w.r.t. F) is unsatisfiable. Note that the maximality here is the set maximality and not the maximum cardinality as in the MaxSAT problem. Consequently, there can be up to 2^|F| many MSSes of F (this is the maximum number of pair-wise incomparable subsets of F). 
This tool also counts the number of Minimal Correction Subsets (MCSes) of F, where a subset N of F is an MCS iff F\N is satisfiable and for every proper subset N' of N, the set F\N' is unsatisfiable. Note that the MCSes of F are exactly the complements of MSSes of F, hence, the number of MSSes and MCSes of F is the same. 

# Related Tools
To the best of our knowledge, our MSS counting approach is the very first (and currently the only) counting approach that does not rely on explicit MSS enumeration; the alternative contemporary approach is to simply enumerate all MSSes via an MSS enumeration tool. However, since there can be up to exponentially many MSSes w.r.t. |F|, the complete enumeration is often practically intractable, and hence, in such cases, the enumeration tools cannot be used to obtain the count. Based on our experimental study, whereas MSS enumerators are able to identify only millions of MSSes within a reasonable time limit, our approach scales even to instances with trillions of MSSes. On the other hand, our approach scales only to instances with low thousands clauses in the input formula. Therefore, our approach (tool) is suitable for instances that are large in the MSS count but relatively small in the number of clauses. In case you need to deal with instances that contain much larger number of clauses, we recommed to employ our contemporary MSS enumerator [RIME](https://github.com/jar-ben/rime). 

# Citation
A paper that introduces our counting approach was accepted to AAAI 2021 (to appear). If you use the tool, please, cite our paper:

```
@inproceedings{BendikMeel2021,
  author    = {Jaroslav Bend{\'{\i}}k and
               Kuldeep S. Meel},
  title     = {Counting Maximal Satisfiable Subsets},
  booktitle = {AAAI},
  year      = {2021 (to appear)}
}
```
