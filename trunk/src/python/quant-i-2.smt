(forall ((i Int))
  (let ((a!1 (or (not (= (q i) idle))
                 (not (= (x i) 0.0))
                 (not (&gt;= (last i) 0.0))
                 (not (&gt;= (first i) 0.0))
                 (not (not (= g i)))))
        (a!2 (or (not (= (q i) start))
                 (not (= (x i) 0.0))
                 (not (not (= g i)))
                 (not (&gt;= (first i) 0.0))
                 (not (= (last i) 5.0))))
        (a!3 (or (not (= (q i) start))
                 (not (= (last i) 5.0))
                 (not (= (x i) 0.0))
                 (not (not (= g i)))
                 (not (&gt;= (first i) 0.0))))
        (a!4 (or (not (= (q i) start))
                 (not (&gt;= (first i) 0.0))
                 (not (= (last i) 5.0))
                 (not (= (x i) 0.0))
                 (not (not (= g i)))))
        (a!5 (or (not (= (q i) start))
                 (not (not (= g i)))
                 (not (&gt;= (first i) 0.0))
                 (not (= (last i) 5.0))
                 (not (= (x i) 0.0))))
        (a!6 (or (not (= (q i) check))
                 (not (= (first i) 7.0))
                 (not (= (x i) 0.0))
                 (not (= g i))
                 (not (&gt;= (last i) 0.0))))
        (a!7 (or (not (= (q i) check))
                 (not (&gt;= (last i) 0.0))
                 (not (= (first i) 7.0))
                 (not (= (x i) 0.0))
                 (not (= g i))))
        (a!8 (or (not (= (q i) check))
                 (not (= g i))
                 (not (&gt;= (last i) 0.0))
                 (not (= (first i) 7.0))
                 (not (= (x i) 0.0))))
        (a!9 (or (not (= (q i) check))
                 (not (= (x i) 0.0))
                 (not (= g i))
                 (not (&gt;= (last i) 0.0))
                 (not (= (first i) 7.0))))
        (a!10 (or (not (= idle (q i)))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not (= (first i) 0.0))
                  (not (not (= g i)))))
        (a!11 (or (not (= idle (q i)))
                  (not (= (x i) 0.0))
                  (not (not (= g i)))
                  (not (&gt;= (last i) 0.0))
                  (not (&gt;= (first i) 0.0))))
        (a!12 (or (not (= idle (q i)))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not ((not (= g i))))
                  (not (&gt;= (last i) 0.0))))
        (a!13 (or (not (= idle (q i)))
                  (not (&gt;= (last i) 0.0))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not (not (= g i)))))
        (a!14 (or (not (= idle (q i)))
                  (not (&gt;= (last i) 0.0))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not ((not (= g i))))))
        (a!15 (or (not (= idle (q i)))
                  (not ((not (= g i))))
                  (not (&gt;= (last i) 0.0))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))))
        (a!16 (or (not (= idle (q i)))
                  (not (= (x i) 0.0))
                  (not ((not (= g i))))
                  (not (&gt;= (last i) 0.0))
                  (not (&gt;= (first i) 0.0))))
        (a!17 (or (not (= start (q i)))
                  (not (not (= g i)))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))))
        (a!18 (or (not (= start (q i)))
                  (not (= (last i) 5.0))
                  (not ((not (= g i))))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))))
        (a!19 (or (not (= start (q i)))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not (not (= g i)))
                  (not (&gt;= (first i) 0.0))))
        (a!20 (or (not (= start (q i)))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not ((not (= g i))))
                  (not (&gt;= (first i) 0.0))))
        (a!21 (or (not (= start (q i)))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not (not (= g i)))))
        (a!22 (or (not (= start (q i)))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not ((not (= g i))))))
        (a!23 (or (not (= idle (q i)))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not (= (first i) 0.0))
                  (not ((not (= g i))))))
        (a!24 (or (not (= idle (q i)))
                  (not (not (= g i)))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not (= (first i) 0.0))))
        (a!25 (or (not (= idle (q i)))
                  (not (= (first i) 0.0))
                  (not ((not (= g i))))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))))
        (a!26 (or (not (= idle (q i)))
                  (not (= (last i) 5.0))
                  (not (= (first i) 0.0))
                  (not ((not (= g i))))
                  (not (= (x i) 0.0))))
        (a!27 (or (not (= idle (q i)))
                  (not (not (= g i)))
                  (not (&gt;= (last i) 0.0))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))))
        (a!28 (or (not (= start (q i)))
                  (not ((not (= g i))))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))))
        (a!29 (or (not (= start (q i)))
                  (not (= (last i) 5.0))
                  (not (not (= g i)))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))))
        (a!30 (or (not (= idle (q i)))
                  (not (= (last i) 5.0))
                  (not (= (first i) 0.0))
                  (not (not (= g i)))
                  (not (= (x i) 0.0))))
        (a!31 (or (not (= idle (q i)))
                  (not (&gt;= (first i) 0.0))
                  (not (= (x i) 0.0))
                  (not (not (= g i)))
                  (not (&gt;= (last i) 0.0))))
        (a!32 (or (not (= idle (q i)))
                  (not ((not (= g i))))
                  (not (= (x i) 0.0))
                  (not (= (last i) 5.0))
                  (not (= (first i) 0.0)))))
    (=&gt; (and (&gt;= i 1) (&lt;= i N))
        (or (not a!1)
            (not a!2)
            (not a!3)
            (not a!4)
            (not a!5)
            (not a!6)
            (not a!7)
            (not a!8)
            (not a!9)
            (not a!10)
            (not a!11)
            (not a!12)
            (not a!13)
            (not a!14)
            (not a!15)
            (not a!16)
            (not a!17)
            (not a!18)
            (not a!19)
            (not a!20)
            (not a!21)
            (not a!22)
            (not a!23)
            (not a!24)
            (not a!25)
            (not a!26)
            (not a!27)
            (not a!28)
            (not a!29)
            (not a!30)
            (not a!31)
            (not a!32)))))