(define (problem BLOCKS-z3)
(:domain BLOCKS)
(:objects H G F E C B D A )
(:INIT (ON A B) (ON B C) (ON C D) (ON D E) (ON E F) (ON F G) (ON G H)
 (CLEAR A) (ONTABLE H) (HANDEMPTY))
(:goal (AND (ON H G) (ON G F) (ON F E) (ON E D) (ON D C) (ON C B) (ON B A)))
)