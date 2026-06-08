  $ . ../setup-project.sh
  $ rocq compile test.v
  For C -> 
  In the database bool: nothing
  In the database core: nothing
  In the database eq_true: nothing
  In the database extcore: nothing
  In the database rewrite: nothing
  In the database rewrite_instances: nothing
  In the database test:
    exact Cu' (cost 0, pattern C unit' tt', id 0)
    exact Cu (cost 0, pattern C unit tt, id 0)
  In the database typeclass_instances:
    exact Cu' (cost 0, pattern C unit' tt', id 0)
  
  Db: test
  Class: C
  Transparent terms per depth:
  Depth 1
    tt' (modes {}) in Hint Resolve [Exact] (exact Cu')
    unit' (modes {}) in Hint Resolve [Exact] (exact Cu')
  Db: test
  Class: C
  Transparent terms per depth:
  Depth 1
    test.tt' (modes {}) in Hint Resolve [Exact] (exact Cu')
    test.unit' (modes {}) in Hint Resolve [Exact] (exact Cu')
  Db: test
  Class: C
  Transparent terms per depth:
  Depth 1
    tt' (modes {-}) in Hint Resolve [Exact] (exact Cu')
    unit' (modes {!}) in Hint Resolve [Exact] (exact Cu')
  Db: test
  Class: C
  Transparent terms per depth:
  Depth 1
    unit' (modes {!}) in Hint Resolve [Exact] (exact Cu')
  Db: test
  Class: C
  No transparent terms found.
