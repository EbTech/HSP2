; woodworking task with 18 parts and 140% wood
; Machines:
;   1 grinder
;   1 glazer
;   1 immersion-varnisher
;   1 planer
;   1 highspeed-saw
;   1 spray-varnisher
;   1 saw
; random seed: 859097

(define (problem wood-prob-s06)
  (:domain woodworking)
  (:objects
    grinder0 - grinder
    glazer0 - glazer
    immersion-varnisher0 - immersion-varnisher
    planer0 - planer
    highspeed-saw0 - highspeed-saw
    spray-varnisher0 - spray-varnisher
    saw0 - saw
    white blue green black mauve red - acolour
    mahogany oak pine walnut teak - awood
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 - part
    b0 b1 b2 b3 b4 b5 b6 - board
    s0 s1 s2 s3 s4 s5 s6 s7 s8 - aboardsize
  )
  (:init
    (grind-treatment-change varnished colourfragments)
    (grind-treatment-change glazed untreated)
    (grind-treatment-change untreated untreated)
    (grind-treatment-change colourfragments untreated)
    (is-smooth smooth)
    (is-smooth verysmooth)
    
    (boardsize-successor s0 s1)
    (boardsize-successor s1 s2)
    (boardsize-successor s2 s3)
    (boardsize-successor s3 s4)
    (boardsize-successor s4 s5)
    (boardsize-successor s5 s6)
    (boardsize-successor s6 s7)
    (boardsize-successor s7 s8)
    (has-colour glazer0 natural)
    (has-colour glazer0 white)
    (has-colour glazer0 green)
    (has-colour glazer0 red)
    (has-colour glazer0 black)
    (has-colour immersion-varnisher0 black)
    (has-colour immersion-varnisher0 white)
    (has-colour immersion-varnisher0 natural)
    (has-colour immersion-varnisher0 red)
    (empty highspeed-saw0)
    (has-colour spray-varnisher0 black)
    (has-colour spray-varnisher0 white)
    (has-colour spray-varnisher0 natural)
    (has-colour spray-varnisher0 red)
    (unused p0)
    (goalsize p0 medium)
    
    
    
    
    (available p1)
    (colour p1 green)
    (wood p1 teak)
    (surface-condition p1 verysmooth)
    (treatment p1 varnished)
    (goalsize p1 large)
    
    
    
    
    (available p2)
    (colour p2 mauve)
    (wood p2 mahogany)
    (surface-condition p2 smooth)
    (treatment p2 glazed)
    (goalsize p2 large)
    
    
    
    
    (unused p3)
    (goalsize p3 small)
    
    
    
    
    (unused p4)
    (goalsize p4 medium)
    
    
    
    
    (unused p5)
    (goalsize p5 medium)
    
    
    
    
    (unused p6)
    (goalsize p6 large)
    
    
    
    
    (available p7)
    (colour p7 blue)
    (wood p7 pine)
    (surface-condition p7 rough)
    (treatment p7 colourfragments)
    (goalsize p7 medium)
    
    
    
    
    (unused p8)
    (goalsize p8 small)
    
    
    
    
    (unused p9)
    (goalsize p9 medium)
    
    
    
    
    (unused p10)
    (goalsize p10 small)
    
    
    
    
    (unused p11)
    (goalsize p11 large)
    
    
    
    
    (unused p12)
    (goalsize p12 small)
    
    
    
    
    (unused p13)
    (goalsize p13 small)
    
    
    
    
    (unused p14)
    (goalsize p14 medium)
    
    
    
    
    (unused p15)
    (goalsize p15 medium)
    
    
    
    
    (unused p16)
    (goalsize p16 small)
    
    
    
    
    (unused p17)
    (goalsize p17 small)
    
    
    
    
    (boardsize b0 s3)
    (wood b0 teak)
    (surface-condition b0 rough)
    (available b0)
    (boardsize b1 s6)
    (wood b1 mahogany)
    (surface-condition b1 rough)
    (available b1)
    (boardsize b2 s6)
    (wood b2 oak)
    (surface-condition b2 smooth)
    (available b2)
    (boardsize b3 s8)
    (wood b3 pine)
    (surface-condition b3 rough)
    (available b3)
    (boardsize b4 s4)
    (wood b4 pine)
    (surface-condition b4 rough)
    (available b4)
    (boardsize b5 s8)
    (wood b5 walnut)
    (surface-condition b5 rough)
    (available b5)
    (boardsize b6 s2)
    (wood b6 walnut)
    (surface-condition b6 rough)
    (available b6)
  )
  (:goal
    (and
      (available p0)
      (wood p0 walnut)
      (surface-condition p0 verysmooth)
      (available p1)
      (colour p1 natural)
      (wood p1 teak)
      (surface-condition p1 verysmooth)
      (available p2)
      (colour p2 natural)
      (surface-condition p2 verysmooth)
      (treatment p2 glazed)
      (available p3)
      (colour p3 black)
      (wood p3 pine)
      (surface-condition p3 verysmooth)
      (treatment p3 varnished)
      (available p4)
      (colour p4 green)
      (wood p4 pine)
      (surface-condition p4 smooth)
      (treatment p4 glazed)
      (available p5)
      (wood p5 walnut)
      (surface-condition p5 verysmooth)
      (treatment p5 glazed)
      (available p6)
      (colour p6 red)
      (wood p6 oak)
      (surface-condition p6 smooth)
      (treatment p6 varnished)
      (available p7)
      (wood p7 pine)
      (treatment p7 glazed)
      (available p8)
      (surface-condition p8 smooth)
      (treatment p8 glazed)
      (available p9)
      (colour p9 white)
      (wood p9 pine)
      (available p10)
      (colour p10 black)
      (wood p10 oak)
      (treatment p10 glazed)
      (available p11)
      (colour p11 natural)
      (wood p11 pine)
      (available p12)
      (wood p12 walnut)
      (surface-condition p12 verysmooth)
      (available p13)
      (colour p13 natural)
      (surface-condition p13 smooth)
      (available p14)
      (wood p14 mahogany)
      (treatment p14 glazed)
      (available p15)
      (wood p15 mahogany)
      (surface-condition p15 verysmooth)
      (available p16)
      (colour p16 natural)
      (treatment p16 varnished)
      (available p17)
      (colour p17 red)
      (wood p17 teak)
    )
  )
  
)
