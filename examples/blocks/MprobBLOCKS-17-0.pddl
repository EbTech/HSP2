(define (problem BLOCKS-17-0-a)
(:domain BLOCKS)
(:objects C D E F B I J A N O K M P H G L Q )
(:INIT (CLEAR P) (ONTABLE M)
 (ON Q A) (ON A J) (ON J I)
 (ON I B) (ON B M) (ON L F) (ON F E) (ON E K) (ON G D) (ON D C) (ON C O)
 (ON H N) (ON K Q) (ON O L) (ON N G) (ON P H) (HANDEMPTY))
(:goal (AND (ON Q N) (ON N L) (ON L O) (ON O J) (ON J H) (ON H C) (ON C E)
            (ON E M) (ON P A) (ON A G) (ON G B) (ON B I) (ON I K)
            (ON K F) (ON F D)))
)
