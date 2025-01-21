# TODO Sketch for the Chapter

## intro
- predicates for information hiding in api
- information hiding 
- abstraction function

Introduce the running example of Linked List
- showcase supported operations (client code)
- not doubly linked like in stdlib
    - maybe footnote https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Adrian_Jenny_PW_Report.pdf

## predicates
  - abstract memory access and implementation details
  -     (with binary tree?, viper has linked list)
 - example list(link *List)
recursive
Resource
fold
 - might fail
unfold
 - might fail

(omit abstract predicate)

## Mem predicate
With Receiver
what it represents, "token"
can be passed by clients (without knowing exactly which permission it "contains")
In pre post of e.g. NewList, add elem
Explain how this helps information hiding

## unfolding
unfolding in PURE_EXPRESSION (why must it be pure?)

necessity: in pure functions (because of syntactical restrictions can't use a statement to unfold)

Example:  like Front/Head?

## Full specifications with abstraction function
--> link to Appendix
abstraction function to a mathematical object
Implementing `View` to a sequence 


## predicates as termination measures
predicate
finite, but possibly unbounded number ==> only later for predicate termination

e.g. for Length
- iterative length / or getting last element
  - seen how to write a (recursive) function to get the length of a linked list
  - this function preserved access to the linked list
  - if we write an iterative version
  - traversing the list we must unfold access
  - it is not clear how we could fold it back to return back the full permission to the list
  - this can be achieved by using _magic wands_ , an advanced topic (link)
  - Example: iterative length without ensures Mem ...
  
## Full LL example
  with client


# Appendix
## Builtin Mathematical Types (...)
examples with sequence
Reference: (seq, set, mset, dict)
- operations
- conversions
