(forall ((i Int) (j Int))
  (let ((a!1 (or (and (= (q i) start) (= idle (q j)) (= x 1))
                 (and (= (q i) cs) (= idle (q j)) (= x 0))
                 (and (= (q i) start) (= start (q j)) (= x 1))
                 (and (= (q i) idle) (= idle (q j)) (= x 1))
                 (and (= (q i) cs) (= start (q j)) (= x 0))
                 (and (= (q i) start) (= cs (q j)) (= x 0))
                 (and (= (q i) start) (= idle (q j)) (= x 0))
                 (and (= (q i) idle) (= start (q j)) (= x 1))
                 (and (= (q i) start) (= start (q j)) (= x 0))
                 (and (= (q j) start) (= idle (q i)) (= x 1))
                 (and (= (q j) start) (= start (q i)) (= x 1))
                 (and (= (q j) cs) (= idle (q i)) (= x 0))
                 (and (= (q j) start) (= cs (q i)) (= x 0))
                 (and (= (q j) cs) (= start (q i)) (= x 0))
                 (and (= (q j) start) (= idle (q i)) (= x 0))
                 (and (= (q j) idle) (= start (q i)) (= x 1))
                 (and (= (q j) start) (= start (q i)) (= x 0))
                 (and (= idle (q i)) (= idle (q j)) (= x 1))
                 (and (= idle (q i)) (= idle (q j)) (= x 0))
                 (and (= start (q i)) (= idle (q j)) (= x 1))
                 (and (= start (q i)) (= idle (q j)) (= x 0))
                 (and (= idle (q i)) (= start (q j)) (= x 1))
                 (and (= idle (q i)) (= start (q j)) (= x 0))
                 (and (= cs (q i)) (= idle (q j)) (= x 0))
                 (and (= start (q i)) (= start (q j)) (= x 1))
                 (and (= start (q i)) (= start (q j)) (= x 0))
                 (and (= idle (q i)) (= cs (q j)) (= x 0))
                 (and (= cs (q i)) (= start (q j)) (= x 0))
                 (and (= start (q i)) (= cs (q j)) (= x 0)))))
    (=&gt; (and (&gt;= i 1) (&lt;= i N) (&gt;= j 1) (&lt;= j N) (distinct i j)) a!1)))