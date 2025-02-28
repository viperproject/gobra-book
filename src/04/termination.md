# Interfaces and termination

- interface method terminates ==> implementation method must terminate
  - ok: no decreases , decreases
  - error: decreases, no decreases
    E.g., no termination measure for `(s IntSlice) Swap`
    ``` text
    ERROR Generated implementation proof (IntSlice implements interface{ View, Len, LessSpec, Less, LessIsConnected, LessIsTransitive, Swap }) failed. Function might not terminate. 

    Required termination condition might not hold.
    ```
    examples from [sort.Interface case study](./sort.md)
  - termination measure must be comparable (open issue)
    - implementation's measure must be "smaller"
    - e.g. `decreases 10` and `decreases 1`


> If an interface method has a termination measure specified, the implementing method must have a termination measure that is at least as strong.
