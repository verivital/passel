(forall ((i Int) (j Int))
  (let ((a!1 (and (not (&lt;= (x j) 0.0))
                  (&lt;= 0 N)
                  (= (x i) 0.0)
                  (= (q i) start)
                  (= idle (q j))
                  (&gt;= g 0)
                  (&lt;= g 0)))
        (a!3 (or (and (= (x i) 0.0)
                      (= (q i) start)
                      (= idle (q j))
                      (&gt;= g 0)
                      (&lt;= g 0))
                 (and (= (x j) 0.0)
                      (= (q j) start)
                      (= idle (q i))
                      (&gt;= g 0)
                      (&lt;= g 0))))
        (a!4 (and (not (&lt;= 0.0 (x j)))
                  (&lt;= (x j) 0.0)
                  (&gt;= (x j) 0.0)
                  (&lt;= (x i) 0.0)))
        (a!6 (and (not (&lt;= (x i) 0.0)) (&lt;= (x j) 0.0) (&gt;= (x j) 0.0)))
        (a!8 (or (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0))
                 (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0) (&gt;= A 0.0))))
        (a!9 (or (and (&lt;= (x j) 0.0)
                      (&gt;= (x j) 0.0)
                      (&lt;= (x i) 0.0)
                      (&gt;= A 0.0))
                 (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0) (&lt;= (x i) 0.0))))
        (a!12 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (&lt;= (x j) 0.0))
                  (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!13 (and (&lt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x i)))
                   (&lt;= (x i) 0.0)
                   (&gt;= (x i) 0.0)))
        (a!15 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= (x j) 0.0) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!16 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (&lt;= (x j) 0.0))
                  (and (&lt;= (x i) 0.0)
                       (&gt;= (x i) 0.0)
                       (&lt;= (x j) 0.0)
                       (&gt;= A 0.0))))
        (a!17 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (&gt;= A 0.0))
                  (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!21 (and (not (&lt;= 0.0 (x j))) (&gt;= (x j) 0.0)))
        (a!22 (and (&lt;= 0 N)
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= (x j) 0.0)
                   (&lt;= (x i) 0.0)))
        (a!23 (and (not (&lt;= (x i) 0.0)) (not (&lt;= 0.0 (x j))) (&gt;= (x j) 0.0)))
        (a!24 (and (not (&lt;= 0.0 (x j))) (&gt;= (x j) 0.0) (&lt;= (x i) 0.0)))
        (a!25 (and (&lt;= 0 N) (not (&lt;= 0.0 (x j))) (&gt;= (x j) 0.0)))
        (a!26 (and (not (&lt;= 0.0 (x j))) (&gt;= (x j) 0.0) (&gt;= A 0.0)))
        (a!27 (and (not (&lt;= 0.0 (x j)))
                   (&gt;= (x j) 0.0)
                   (&lt;= (x i) 0.0)
                   (&gt;= A 0.0)))
        (a!29 (and (&lt;= 0 N)
                   (&lt;= (x i) 0.0)
                   (&gt;= (x i) 0.0)
                   (not (&lt;= 0.0 (x j)))))
        (a!30 (and (not (&lt;= 0.0 (x j)))
                   (&lt;= 0 N)
                   (&lt;= (x i) 0.0)
                   (&gt;= (x i) 0.0)))
        (a!31 (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (not (&lt;= 0.0 (x j)))))
        (a!33 (and (not (&lt;= 0.0 (x j)))
                   (not (&lt;= 0.0 (x i)))
                   (&lt;= (x i) 0.0)
                   (&gt;= (x i) 0.0)))
        (a!35 (and (not (&lt;= 0.0 (x j))) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0)))
        (a!37 (and (&lt;= (x i) 0.0)
                   (&gt;= (x i) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= A 0.0)))
        (a!43 (and (&lt;= 0 N)
                   (&lt;= (x j) 0.0)
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x i)))))
        (a!44 (and (not (&lt;= 0.0 (x j)))
                   (&lt;= (x j) 0.0)
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x i)))))
        (a!45 (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0) (not (&lt;= 0.0 (x i)))))
        (a!47 (and (&lt;= (x j) 0.0)
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x i)))
                   (&gt;= A 0.0)))
        (a!50 (and (not (&lt;= 0.0 (x i))) (&gt;= (x i) 0.0)))
        (a!51 (and (&lt;= 0 N) (not (&lt;= 0.0 (x i))) (&gt;= (x i) 0.0)))
        (a!52 (and (&lt;= 0 N)
                   (not (&lt;= 0.0 (x i)))
                   (&gt;= (x i) 0.0)
                   (&lt;= (x j) 0.0)))
        (a!53 (and (&lt;= (x j) 0.0)
                   (&lt;= 0 N)
                   (not (&lt;= 0.0 (x i)))
                   (&gt;= (x i) 0.0)))
        (a!54 (and (not (&lt;= 0.0 (x i))) (&gt;= (x i) 0.0) (&lt;= (x j) 0.0)))
        (a!55 (and (&lt;= (x j) 0.0) (not (&lt;= 0.0 (x i))) (&gt;= (x i) 0.0)))
        (a!56 (and (not (&lt;= 0.0 (x i)))
                   (&gt;= (x i) 0.0)
                   (&lt;= (x j) 0.0)
                   (&gt;= A 0.0)))
        (a!57 (and (not (&lt;= 0.0 (x i))) (&gt;= (x i) 0.0) (&gt;= A 0.0)))
        (a!62 (or (not (= (q i) start)) (&lt;= (x i) A)))
        (a!63 (or (not (= (q j) start)) (&lt;= (x j) A)))
        (a!66 (not (&lt;= 0.0 (+ (* (- 1.0) A) (x i)))))
        (a!68 (and (&lt;= 0 N)
                   (= (x i) 0.0)
                   (= (q i) start)
                   (= idle (q j))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (not (&lt;= (x j) 0.0))))
        (a!69 (and (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (= idle (q j))
                   (not (&lt;= (x j) 0.0))
                   (not (&lt;= 0.0 (x j)))))
        (a!70 (and (= (x i) 0.0)
                   (= (q i) start)
                   (= idle (q j))
                   (not (&lt;= (x j) 0.0))
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= g 0)
                   (&lt;= g 0)))
        (a!71 (and (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (= idle (q j))
                   (not (&lt;= (x j) 0.0))
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= A 0.0)))
        (a!72 (and (= (x i) 0.0)
                   (= (q i) start)
                   (= idle (q j))
                   (not (&lt;= (x j) 0.0))
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (&lt;= A 0.0)
                   (&gt;= A 0.0)))
        (a!74 (and (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (= idle (q j))
                   (not (&lt;= (x j) 0.0))
                   (not (&lt;= 0.0 (x j)))
                   (not (&lt;= A 0.0))))
        (a!78 (and (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))))
        (a!79 (and (= (x i) 0.0)
                   (= (q i) start)
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= g 0)
                   (&lt;= g 0)))
        (a!80 (and (not (&lt;= 0.0 (x i))) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0)))
        (a!82 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (&gt;= A 0.0))))
        (a!86 (and (= (x i) 0.0)
                   (= (q i) start)
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (&lt;= A 0.0)
                   (&gt;= A 0.0)))
        (a!89 (and (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= A 0.0)))
        (a!90 (and (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   (not (&lt;= A 0.0))))
        (a!92 (or (and (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&lt;= A 0.0)
                       (&gt;= A 0.0))
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&lt;= A 0.0)
                       (&gt;= A 0.0)))))
  (let ((a!2 (or (and (&lt;= 0 N)
                      (= (x i) 0.0)
                      (= (q i) start)
                      (= idle (q j))
                      (&gt;= g 0)
                      (&lt;= g 0)
                      (&gt;= (x j) 0.0))
                 (and (&lt;= g 0)
                      (&lt;= 0 N)
                      (= (x i) 0.0)
                      (= (q i) start)
                      (= idle (q j))
                      (&gt;= (x j) 0.0)
                      (&lt;= (x j) 0.0)
                      (&gt;= g 0))
                 a!1))
        (a!5 (or a!4 (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0) (&lt;= (x i) 0.0))))
        (a!7 (or a!6 (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0) (&lt;= (x i) 0.0))))
        (a!10 (or (and a!9 (&lt;= (x j) 0.0))
                  (and (&lt;= (x j) 0.0)
                       (&gt;= (x j) 0.0)
                       (&lt;= (x i) 0.0)
                       (&gt;= A 0.0))
                  (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0) (&lt;= (x i) 0.0))))
        (a!14 (or a!13 (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!18 (or (and a!17 (&lt;= (x j) 0.0))
                  (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (&gt;= A 0.0))
                  (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!28 (and (or a!27 a!24) (not (&lt;= 0.0 (x j)))))
        (a!32 (or a!31 (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!34 (or a!33 (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!36 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0)) a!35))
        (a!38 (and a!17 (not (&lt;= 0.0 (x j)))))
        (a!46 (or (and (&gt;= (x i) 0.0) (&lt;= (x j) 0.0) (&gt;= (x j) 0.0)) a!45))
        (a!48 (or (and (or a!47 a!45) (&lt;= (x j) 0.0)) a!47 a!45))
        (a!58 (or (and (or a!57 a!50) (&lt;= (x j) 0.0)) a!57 a!50))
        (a!64 (and (= (q i) idle)
                   (&lt;= g 0)
                   (&gt;= g 0)
                   a!62
                   (= (q j) idle)
                   (&gt;= (x i) 0.0)
                   (not (&lt;= 0.0 (x i)))
                   a!63
                   (not (&lt;= (x i) 0.0))))
        (a!73 (or a!72
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&lt;= A 0.0)
                       (&gt;= A 0.0))))
        (a!81 (or a!80 (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!85 (or a!79
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0))))
        (a!87 (or a!86
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&lt;= A 0.0)
                       (&gt;= A 0.0)))))
  (let ((a!11 (or (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0))
                  (and (&lt;= 0 N) (&lt;= (x j) 0.0) (&gt;= (x j) 0.0) (&lt;= (x i) 0.0))
                  (and (&lt;= 0 N) a!5)
                  (and (&lt;= 0 N) a!7)
                  (and (&lt;= 0 N) (&lt;= (x j) 0.0) (&gt;= (x j) 0.0))
                  (and a!8 (&lt;= 0 N))
                  (and (&lt;= 0 N) a!10)))
        (a!19 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= 0 N) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= 0 N) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (&lt;= (x j) 0.0))
                  (and (&lt;= (x j) 0.0) (&lt;= 0 N) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= 0 N) a!12)
                  (and (&lt;= 0 N) a!14)
                  (and (&lt;= 0 N) a!15)
                  (and a!16 (&lt;= 0 N))
                  (and (&lt;= 0 N) a!18)))
        (a!39 (or a!38
                  (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0) (&gt;= A 0.0))
                  (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))))
        (a!49 (or (and (&lt;= (x j) 0.0) (&gt;= (x j) 0.0))
                  a!43
                  (and (&lt;= 0 N) (or a!44 a!45))
                  (and (&lt;= 0 N) a!46)
                  (and (&lt;= 0 N) (&lt;= (x j) 0.0) (&gt;= (x j) 0.0))
                  (and a!8 (&lt;= 0 N))
                  (and (&lt;= 0 N) a!48)))
        (a!65 (or a!64
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= (x i) 0.0)
                       (&lt;= (x i) 0.0)
                       (&gt;= g 0)
                       (&lt;= g 0))))
        (a!83 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= 0 N) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= 0 N) a!81)
                  (and a!82 (&lt;= 0 N))
                  (and (&lt;= 0 N) a!17))))
  (let ((a!20 (or (and a!3 a!11 a!19)
                  (and (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0))
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0))))
        (a!40 (or (and (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  (and (&lt;= 0 N) (&lt;= (x i) 0.0) (&gt;= (x i) 0.0))
                  a!29
                  a!30
                  (and (&lt;= 0 N) a!32)
                  (and (&lt;= 0 N) a!34)
                  (and (&lt;= 0 N) a!36)
                  (and (or a!31 a!37) (&lt;= 0 N))
                  (and (&lt;= 0 N) a!39)))
        (a!59 (and (&gt;= (x i) 0.0)
                   a!49
                   (or a!50
                       a!51
                       a!52
                       a!53
                       (and (&lt;= 0 N) (or a!54 a!50))
                       (and (&lt;= 0 N) (or a!55 a!50))
                       (and (&lt;= 0 N) (or a!50 a!55))
                       (and (or a!54 a!56) (&lt;= 0 N))
                       (and (&lt;= 0 N) a!58))
                   (= (x i) 0.0)
                   (= (q i) start)
                   (= idle (q j))
                   (&gt;= g 0)
                   (&lt;= g 0)))
        (a!84 (and (not (&lt;= A 0.0))
                   (not (= g i)) (not (= g j))
                   (= idle (q i))
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   a!83))
        (a!88 (and (not (= g i)) (not (= g j))
                   (= idle (q i))
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   (&gt;= A 0.0)
                   a!83))
        (a!91 (and (not (= g i)) (not (= g j))
                   (= idle (q i))
                   (= idle (q j))
                   (&gt;= (x j) 0.0)
                   (not (&lt;= 0.0 (x j)))
                   (not (&lt;= A 0.0))
                   a!83))
        (a!93 (or (and (= idle (q i)) (&gt;= g 0) (&lt;= g 0) (= idle (q j)))
                  (and (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0))
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0))
                  (and (not (&lt;= A 0.0))
                       (not (= g i)) (not (= g j))
                       (= idle (q i))
                       (= idle (q j))
                       a!11
                       a!19)
                  (and a!3 a!11 a!19)
                  (and a!92 (&gt;= A 0.0) a!11 a!19)
                  (and (not (= g i)) (not (= g j))
                       (= idle (q i))
                       (= idle (q j))
                       (&gt;= A 0.0)
                       a!11
                       a!19)
                  (and (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (= idle (q j))
                       (&gt;= A 0.0))
                  (and a!92 (&gt;= A 0.0))
                  (and (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (= idle (q j))
                       (not (&lt;= A 0.0)))
                  (and (not (= g i)) (not (= g j))
                       (= idle (q i))
                       (= idle (q j))
                       (not (&lt;= A 0.0))
                       a!11
                       a!19))))
  (let ((a!41 (and (&gt;= (x j) 0.0)
                   (or a!21
                       a!22
                       (and (&lt;= 0 N) (or a!23 a!24))
                       a!25
                       (and (or a!21 a!26) (&lt;= 0 N))
                       (and (&lt;= 0 N) (or a!28 a!27 a!24)))
                   a!40
                   (= (x j) 0.0)
                   (= (q j) start)
                   (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)))
        (a!60 (or a!59
                  (and (&gt;= (x i) 0.0)
                       (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0))))
        (a!61 (or a!59
                  (and (&gt;= (x i) 0.0)
                       (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0))
                  (and (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0))
                  (and (&gt;= (x i) 0.0) a!11 a!19 a!3)
                  (and (&gt;= (x i) 0.0) a!3)))
        (a!75 (and (= (x j) 0.0)
                   (= (q j) start)
                   (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (or a!21
                       a!22
                       (and (&lt;= 0 N) (or a!23 a!24))
                       a!25
                       (and (or a!21 a!26) (&lt;= 0 N))
                       (and (&lt;= 0 N) (or a!28 a!27 a!24)))
                   a!40))
        (a!76 (and (= (x j) 0.0)
                   (= (q j) start)
                   (= idle (q i))
                   (&gt;= g 0)
                   (&lt;= g 0)
                   (&lt;= A 0.0)
                   (&gt;= A 0.0)
                   (or a!21
                       a!22
                       (and (&lt;= 0 N) (or a!23 a!24))
                       a!25
                       (and (or a!21 a!26) (&lt;= 0 N))
                       (and (&lt;= 0 N) (or a!28 a!27 a!24)))
                   a!40)))
  (let ((a!42 (or a!41
                  (and (&gt;= (x j) 0.0)
                       (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0))))
        (a!77 (or (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0))
                  a!75
                  a!76
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&lt;= A 0.0)
                       (&gt;= A 0.0)))))
  (let ((a!67 (or (and (&lt;= 0 N)
                       (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&gt;= (x i) 0.0)
                       (&gt;= (x j) 0.0))
                  (and (&lt;= 0 N) (&gt;= (x i) 0.0) (&gt;= (x j) 0.0) a!20)
                  (and (&lt;= 0 N) (&gt;= (x i) 0.0) a!42)
                  (and (&lt;= 0 N) (&gt;= (x j) 0.0) a!60)
                  (and (&lt;= 0 N) (&gt;= (x j) 0.0) a!61)
                  (and (&lt;= 0 N) a!65 (&gt;= (x j) 0.0) a!66 (not (&lt;= A 0.0)))
                  (and (&lt;= 0 N)
                       (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&gt;= (x j) 0.0))))
        (a!94 (or a!69
                  a!70
                  (and (= (x j) 0.0)
                       (= (q j) start)
                       (= idle (q i))
                       (&gt;= g 0)
                       (&lt;= g 0))
                  a!71
                  (and a!73 (&gt;= A 0.0))
                  a!74
                  (and a!77 (&gt;= (x j) 0.0))
                  a!78
                  a!79
                  a!84
                  (and a!85 a!83)
                  (and a!87 (&gt;= A 0.0) a!83)
                  a!88
                  a!89
                  (and a!87 (&gt;= A 0.0))
                  a!90
                  a!91
                  (and a!93 (&gt;= (x j) 0.0)))))
  (let ((a!95 (or a!68
                  (and (&lt;= 0 N) (&gt;= (x i) 0.0) a!94)
                  (and (&lt;= 0 N)
                       (= (x i) 0.0)
                       (= (q i) start)
                       (= idle (q j))
                       (&gt;= g 0)
                       (&lt;= g 0)
                       (&gt;= (x j) 0.0)))))
  (let ((a!96 (or (and (not (&lt;= B A))
                       (&lt;= g N)
                       (not (&lt;= A 0.0))
                       (not (&lt;= B 0.0))
                       (&gt;= N 3)
                       (&gt;= (x i) 0.0)
                       (&gt;= (x j) 0.0)
                       (&gt;= g 0)
                       a!2)
                  (and (not (&lt;= B A))
                       (&lt;= g N)
                       (not (&lt;= A 0.0))
                       (not (&lt;= B 0.0))
                       (&gt;= N 3)
                       (&gt;= (x i) 0.0)
                       (&gt;= (x j) 0.0)
                       (&gt;= g 0)
                       a!67)
                  (and (not (&lt;= B A))
                       (&lt;= g N)
                       (not (&lt;= A 0.0))
                       (not (&lt;= B 0.0))
                       (&gt;= N 3)
                       (&gt;= (x i) 0.0)
                       (&gt;= (x j) 0.0)
                       (&gt;= g 0)
                       a!95))))
    (=&gt; (and (&gt;= i 1) (&lt;= i N) (&gt;= j 1) (&lt;= j N) (distinct i j)) a!96)))))))))))