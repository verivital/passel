(forall ((i Int) (j Int))
  (let ((a!1 (or (not (= (q i) fly))
                 (= (q j) base)
                 (not (= (x j) 0.0))

                 
                 (not (= (x i) 0.0))))
        (a!2 (or (not (= (q i) fly))
                 (not (= fly (q j)))
                 (not (= (x j) 28.0))

                 
                 (not (= (x i) 0.0))))
        (a!3 (or (not (= (q i) fly))
                 (not (= (q j) landed))

                 (not (&gt;= (x j) 0.0))
                 
                 (not (= (x i) 0.0))))
        (a!4 (or (not (= (q i) fly))
                 (not (= (q j) fly))

                 (not (&gt;= (x j) 0.0))
                 
                 (not (= (x i) 0.0))))
        (a!5 (or (not (= (q i) fly))
                 (not (= landed (q j)))

                 (not (&gt;= (x j) 0.0))
                 
                 (not (= (x i) 0.0))))
        (a!6 (or (not (= (q i) fly))
                 (not (= fly (q j)))

                 (not (&gt;= (x j) 0.0))
                 
                 (not (= (x i) 0.0))))
        (a!7 (or (not (= (q i) fly))
                 (not (= (q j) fly))
                 (not (= (x j) 28.0))

                 
                 (not (= (x i) 0.0))))
        (a!8 (or (not (= (q i) fly))
                 (not (= (q j) base))
                 (not (= (x j) 28.0))

                 
                 (not (= (x i) 0.0))))
        (a!9 (or (= (q j) base)
                 (not (= (q i) base))

                 (not (&gt;= (x i) 0.0))
                 
                 (not (= (x j) 0.0))))
        (a!10 (or (not (= fly (q j)))
                  (not (= (q i) base))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!11 (or (not (= (q i) base))
                  (not (= fly (q j)))
                  (&lt;= (x j) 0.0)
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!12 (or (not (= (q i) base))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 28.0))))
        (a!13 (or (not (= (q i) base))
                  (not (= base (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x j) 7.0))))
        (a!14 (or (not (= (q i) base))
                  (not (= base (q j)))
                  (not (&gt;= (x j) 7.0))
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!15 (or (not (= landed (q j)))
                  (not (= (q i) base))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!16 (or (not (= (q i) base))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x j) 7.0))))
        (a!17 (or (not (= (q i) base))
                  (not (= fly (q j)))
                  (not (&gt;= (x j) 7.0))
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!18 (or (not (= (q i) base))
                  (not (= fly (q j)))
                  (&lt;= (x j) 7.0)
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!19 (or (not (= (q i) base))
                  (not (= fly (q j)))
                  (not (= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  ))
        (a!20 (or (not (= (q i) base))
                  (not (= base (q j)))
                  (not (&gt;= (x j) 7.0))
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!21 (or (not (= (q i) base))
                  (not (= base (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 28.0))))
        (a!22 (or (not (= (q i) base))
                  (not (= fly (q j)))
                  (not (&gt;= (x j) 7.0))
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!23 (or (not (= (q i) base))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x j) 7.0))))
        (a!24 (or (not (= (q i) base))
                  (not (= base (q j)))
                  (&lt;= (x j) 7.0)
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!25 (or (not (= (q i) base))
                  (not (= base (q j)))
                  (&lt;= (x j) 7.0)
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!26 (or (not (= (q i) base))
                  (not (= fly (q j)))
                  (&lt;= (x j) 7.0)
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!27 (or (not (= (q i) base))
                  (not (= landed (q j)))
                  (&lt;= (x j) 0.0)
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!28 (or (not (= (q i) base))
                  (not (= landed (q j)))
                  (not (= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  ))
        (a!29 (or (not (= (q i) base))
                  (not (= base (q j)))
                  (not (= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  ))
        (a!30 (or (not (= (q i) base))
                  (not (= landed (q j)))
                  (not (&gt;= (x j) 7.0))
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!31 (or (not (= (q i) base))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (&lt;= (x j) 0.0)))
        (a!32 (or (not (= (q i) base))
                  (not (= fly (q j)))
                  (&lt;= (x j) 0.0)
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!33 (or (not (= (q i) base))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!34 (or (not (= (q i) base))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (&lt;= (x j) 0.0)))
        (a!35 (or (not (= (q i) base))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 28.0))))
        (a!36 (or (not (= (q i) base))
                  (not (= landed (q j)))
                  (not (&gt;= (x j) 7.0))
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!37 (or (not (= (q i) base))
                  (not (= landed (q j)))
                  (&lt;= (x j) 7.0)
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!38 (or (not (= (q i) base))
                  (not (= landed (q j)))
                  (&lt;= (x j) 7.0)
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!39 (or (not (= (q i) landed))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!40 (or (not (= (q i) landed))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!41 (or (not (= (q i) base))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!42 (or (not (= (q i) fly))
                  (not (= base (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!43 (or (not (= (q i) landed))
                  (not (= base (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!44 (or (not (= (q j) base))
                  (not (= fly (q i)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!45 (or (not (= fly (q i)))
                  (not (= (q j) fly))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!46 (or (not (= fly (q i)))
                  (not (= (q j) landed))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!47 (or (not (= (q j) fly))
                  (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!48 (or (not (= (q j) landed))
                  (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!49 (or (not (= (q j) base))
                  (not (= base (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x i) 7.0))))
        (a!50 (or (not (= (q j) base))
                  (not (= landed (q i)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!51 (or (not (= fly (q i)))
                  (not (= (q j) base))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!52 (or (not (= (q j) base))
                  (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x i) 7.0))))
        (a!53 (or (not (= (q j) fly))
                  (not (= base (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!54 (or (not (= (q j) landed))
                  (not (= base (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!55 (or (not (= (q j) fly))
                  (not (= landed (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!56 (or (not (= (q j) landed))
                  (not (= landed (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!57 (or (not (= landed (q i)))
                  (not (= (q j) base))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!58 (or (= (q j) base)
                  (not (= fly (q i)))
 
                  
                  (not (= (x i) 0.0))
                  (not (= (x j) 0.0))))
        (a!59 (or (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!60 (or (not (= fly (q j)))
                  (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!61 (or (not (= base (q j)))
                  (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!62 (or (not (= landed (q j)))
                  (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!63 (or (= (q j) base)
                  (not (= fly (q i)))
 
                  
                  (not (= (x j) 0.0))
                  (not (= (x i) 0.0))))
        (a!64 (or (not (= fly (q i)))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!65 (or (not (= fly (q i)))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!66 (or (not (= fly (q i)))
                  (not (= base (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x j) 7.0))
                  (not (= (x i) 0.0))))
        (a!67 (or (not (= fly (q i)))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (&lt;= (x j) 0.0)
                  (not (= (x i) 0.0))))
        (a!68 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (&gt;= (x j) 7.0))
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!69 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (&gt;= (x j) 7.0))
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!70 (or (not (= fly (q i)))
                  (not (= base (q j)))
 
                  
                  (not (= (x i) 0.0))
                  (not (= (x j) 28.0))))
        (a!71 (or (not (= fly (q i)))
                  (not (= fly (q j)))
 
                  
                  (not (= (x i) 0.0))
                  (not (= (x j) 28.0))))
        (a!72 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (= (x j) 28.0))
 
                  
                  (not (= (x i) 0.0))))
        (a!73 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (&lt;= (x j) 7.0)
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!74 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (&lt;= (x j) 7.0)
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!75 (or (not (= fly (q i)))
                  (not (= fly (q j)))
 
                  
                  (not (= (x j) 0.0))
                  (not (= (x i) 0.0))))
        (a!76 (or (not (= fly (q i)))
                  (not (= base (q j)))
 
                  
                  (not (= (x j) 28.0))
                  (not (= (x i) 0.0))))
        (a!77 (or (not (= fly (q i)))
                  (not (= fly (q j)))
 
                  
                  (not (= (x j) 28.0))
                  (not (= (x i) 0.0))))
        (a!78 (or (not (= fly (q i)))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (&lt;= (x j) 0.0)
                  (not (= (x i) 0.0))))
        (a!79 (or (not (= fly (q i)))
                  (not (= landed (q j)))
 
                  
                  (not (= (x j) 28.0))
                  (not (= (x i) 0.0))))
        (a!80 (or (= (q j) base)
                  (not (= fly (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!81 (or (not (= fly (q j)))
                  (not (= base (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!82 (or (not (= landed (q j)))
                  (not (= base (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!83 (or (not (= base (q i)))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (&gt;= (x i) 7.0))
                  (not (= (x j) 0.0))))
        (a!84 (or (not (= base (q i)))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (&gt;= (x i) 7.0))
                  (not (= (x j) 0.0))))
        (a!85 (or (not (= landed (q i)))
                  (not (= fly (q j)))
 
                  
                  (not (= (x j) 0.0))
                  (not (= (x i) 0.0))))
        (a!86 (or (not (= fly (q j)))
                  (not (= landed (q i)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!87 (or (not (= landed (q i)))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x j) 0.0))
                  
                  (not (= (x i) 0.0))))
        (a!88 (or (not (= fly (q i)))
                  (not (= fly (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!89 (or (not (= fly (q i)))
                  (not (= landed (q j)))
 
                  
                  (not (= (x j) 0.0))
                  (not (= (x i) 0.0))))
        (a!90 (or (not (= fly (q i)))
                  (not (= landed (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 0.0))))
        (a!91 (or (not (= fly (q i)))
                  (not (= base (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x j) 7.0))))
        (a!92 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (&gt;= (x j) 7.0))
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!93 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  ))
        (a!94 (or (not (= fly (q i)))
                  (not (= base (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (= (x j) 28.0))))
        (a!95 (or (not (= fly (q i)))
                  (not (= base (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x i) 7.0))
                  (not (&gt;= (x j) 7.0))))
        (a!96 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (&gt;= (x j) 7.0))
                  (not (&lt;= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  ))
        (a!97 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (&gt;= (x j) 7.0))
                  (&gt;= (x j) 28.0)
 
                  (not (&gt;= (x i) 0.0))
                  (not (&gt;= (x j) 0.0))
                  
                  (not (&gt;= (x i) 7.0))))
        (a!98 (or (not (= fly (q i)))
                  (not (= base (q j)))
                  (not (= (x j) 28.0))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (&gt;= (x i) 7.0))))
        (a!99 (or (not (= fly (q i)))
                  (not (= base (q j)))
 
                  (not (&gt;= (x i) 0.0))
                  
                  (not (&gt;= (x i) 7.0))
                  (not (= (x j) 28.0))))
        (a!100 (or (not (= fly (q i)))
                   (not (= base (q j)))
                   (&lt;= (x j) 7.0)
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   ))
        (a!101 (or (not (= fly (q i)))
                   (not (= base (q j)))
                   (not (&gt;= (x j) 7.0))
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!102 (or (not (= fly (q i)))
                   (not (= base (q j)))
                   (&lt;= (x j) 7.0)
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   ))
        (a!103 (or (not (= fly (q i)))
                   (not (= base (q j)))
                   (&lt;= (x j) 7.0)
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!104 (or (not (= fly (q i)))
                   (not (= base (q j)))
                   (&lt;= (x j) 7.0)
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!105 (or (not (= base (q i)))
                   (not (= fly (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!106 (or (not (= base (q i)))
                   (not (= fly (q j)))
                   (&lt;= (x j) 0.0)
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!107 (or (not (= base (q i)))
                   (not (= fly (q j)))
                   (&lt;= (x j) 0.0)
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!108 (or (not (= base (q i)))
                   (not (= fly (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (not (= (x j) 28.0))))
        (a!109 (or (not (= base (q i)))
                   (not (= fly (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (not (&gt;= (x j) 7.0))))
        (a!110 (or (not (= base (q i)))
                   (not (= fly (q j)))
                   (not (&gt;= (x j) 7.0))
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!111 (or (not (= base (q i)))
                   (not (= fly (q j)))
                   (not (= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!112 (or (not (= base (q i)))
                   (not (= fly (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (&lt;= (x j) 0.0)))
        (a!113 (or (not (= base (q i)))
                   (not (= fly (q j)))
                   (&lt;= (x j) 7.0)
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!114 (or (not (= base (q i)))
                   (not (= fly (q j)))
                   (&lt;= (x j) 7.0)
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!115 (or (not (= base (q i)))
                   (not (= fly (q j)))
                   (not (&gt;= (x j) 7.0))
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!116 (or (not (= base (q i)))
                   (not (= landed (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!117 (or (not (= base (q i)))
                   (not (= landed (q j)))
                   (&lt;= (x j) 0.0)
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!118 (or (not (= base (q i)))
                   (not (= landed (q j)))
                   (&lt;= (x j) 0.0)
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!119 (or (not (= base (q i)))
                   (not (= landed (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (not (= (x j) 28.0))))
        (a!120 (or (not (= base (q i)))
                   (not (= landed (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (not (&gt;= (x j) 7.0))))
        (a!121 (or (not (= base (q i)))
                   (not (= landed (q j)))
                   (not (&gt;= (x j) 7.0))
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!122 (or (not (= base (q i)))
                   (not (= landed (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (&lt;= (x j) 0.0)))
        (a!123 (or (not (= base (q i)))
                   (not (= landed (q j)))
                   (not (&gt;= (x j) 7.0))
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!124 (or (not (= base (q i)))
                   (not (= landed (q j)))
                   (&lt;= (x j) 7.0)
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!125 (or (not (= base (q i)))
                   (not (= landed (q j)))
                   (not (= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!126 (or (not (= base (q i)))
                   (not (= base (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (not (&gt;= (x j) 7.0))))
        (a!127 (or (not (= base (q i)))
                   (not (= base (q j)))
                   (not (&gt;= (x j) 7.0))
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!128 (or (not (= base (q i)))
                   (not (= base (q j)))
                   (not (= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!129 (or (not (= base (q j)))
                   (not (= base (q i)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   ))
        (a!130 (or (not (= base (q i)))
                   (not (= base (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (&gt;= (x i) 7.0))
                   (not (= (x j) 28.0))))
        (a!131 (or (not (= base (q i)))
                   (not (= base (q j)))
                   (not (&gt;= (x j) 7.0))
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!132 (or (not (= base (q i)))
                   (not (= base (q j)))
                   (&lt;= (x j) 7.0)
                   (&gt;= (x j) 28.0)
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!133 (or (not (= base (q i)))
                   (not (= base (q j)))
                   (&lt;= (x j) 7.0)
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!134 (or (not (= base (q j)))
                   (not (= landed (q i)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   ))
        (a!135 (or (not (= landed (q i)))
                   (not (= base (q j)))
  
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x j) 7.0))
                   (not (= (x i) 0.0))))
        (a!136 (or (not (= landed (q i)))
                   (not (= fly (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (= (x j) 0.0))))
        (a!137 (or (not (= base (q i)))
                   (not (= landed (q j)))
                   (&lt;= (x j) 7.0)
                   (not (&lt;= (x j) 28.0))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x i) 7.0))))
        (a!138 (or (not (= landed (q i)))
                   (not (= landed (q j)))
  
                   
                   (not (= (x j) 0.0))
                   (not (= (x i) 0.0))))
        (a!139 (or (not (= landed (q j)))
                   (not (= landed (q i)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   ))
        (a!140 (or (not (= landed (q i)))
                   (not (= landed (q j)))
  
                   (not (&gt;= (x j) 0.0))
                   
                   (not (= (x i) 0.0))))
        (a!141 (or (not (= landed (q i)))
                   (not (= landed (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   
                   (not (= (x j) 0.0))))
        (a!142 (or (not (= landed (q i)))
                   (not (= base (q j)))
  
                   (not (&gt;= (x i) 0.0))
                   (not (&gt;= (x j) 0.0))
                   
                   (not (&gt;= (x j) 7.0)))))
    (=&gt; (and (&gt;= i 1) (&lt;= i N) (&gt;= j 1) (&lt;= j N) (distinct i j))
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
            (not a!32)
            (not a!33)
            (not a!34)
            (not a!35)
            (not a!36)
            (not a!37)
            (not a!38)
            (not a!39)
            (not a!40)
            (not a!41)
            (not a!42)
            (not a!43)
            (not a!44)
            (not a!45)
            (not a!46)
            (not a!47)
            (not a!48)
            (not a!49)
            (not a!50)
            (not a!51)
            (not a!52)
            (not a!53)
            (not a!54)
            (not a!55)
            (not a!56)
            (not a!57)
            (not a!58)
            (not a!59)
            (not a!60)
            (not a!61)
            (not a!62)
            (not a!63)
            (not a!64)
            (not a!65)
            (not a!66)
            (not a!67)
            (not a!68)
            (not a!69)
            (not a!70)
            (not a!71)
            (not a!72)
            (not a!73)
            (not a!74)
            (not a!75)
            (not a!76)
            (not a!77)
            (not a!78)
            (not a!79)
            (not a!80)
            (not a!81)
            (not a!82)
            (not a!83)
            (not a!84)
            (not a!85)
            (not a!86)
            (not a!87)
            (not a!88)
            (not a!89)
            (not a!90)
            (not a!91)
            (not a!92)
            (not a!93)
            (not a!94)
            (not a!95)
            (not a!96)
            (not a!97)
            (not a!98)
            (not a!99)
            (not a!100)
            (not a!101)
            (not a!102)
            (not a!103)
            (not a!104)
            (not a!105)
            (not a!106)
            (not a!107)
            (not a!108)
            (not a!109)
            (not a!110)
            (not a!111)
            (not a!112)
            (not a!113)
            (not a!114)
            (not a!115)
            (not a!116)
            (not a!117)
            (not a!118)
            (not a!119)
            (not a!120)
            (not a!121)
            (not a!122)
            (not a!123)
            (not a!124)
            (not a!125)
            (not a!126)
            (not a!127)
            (not a!128)
            (not a!129)
            (not a!130)
            (not a!131)
            (not a!132)
            (not a!133)
            (not a!134)
            (not a!135)
            (not a!136)
            (not a!137)
            (not a!138)
            (not a!139)
            (not a!140)
            (not a!141)
            (not a!142)))))