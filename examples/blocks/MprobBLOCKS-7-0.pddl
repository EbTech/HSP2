(define (problem BLOCKS-7-0)
(:domain BLOCKS)
(:objects C F A B G D E )
(:INIT (CLEAR E) (ONTABLE D) (CLEAR G) (ONTABLE G) (CLEAR B) (ON B A) (ON A F) (ON F C)
 (ON C D) (HANDEMPTY))
(:goal (AND (ON A G) (ON G D) (ON D B) (ON B C) (ON C F) (ON F E)))
)
