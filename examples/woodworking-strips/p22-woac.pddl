; woodworking task with 6 parts and 100% wood
; Machines:
;   1 grinder
;   1 glazer
;   1 immersion-varnisher
;   1 planer
;   1 highspeed-saw
;   1 spray-varnisher
;   1 saw
; random seed: 93985

(define (problem wood-prob-s22)
  (:domain woodworking)
  (:objects
    grinder0 - grinder
    glazer0 - glazer
    immersion-varnisher0 - immersion-varnisher
    planer0 - planer
    highspeed-saw0 - highspeed-saw
    spray-varnisher0 - spray-varnisher
    saw0 - saw
    mauve black blue green - acolour
    teak walnut - awood
    p0 p1 p2 p3 p4 p5 - part
    b0 b1 - board
    s0 s1 s2 s3 s4 - aboardsize
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
    (has-colour glazer0 blue)
    (has-colour glazer0 green)
    (has-colour glazer0 natural)
    (has-colour immersion-varnisher0 blue)
    (has-colour immersion-varnisher0 mauve)
    (has-colour immersion-varnisher0 black)
    (empty highspeed-saw0)
    (has-colour spray-varnisher0 blue)
    (has-colour spray-varnisher0 mauve)
    (has-colour spray-varnisher0 black)
    (available p0)
    (colour p0 green)
    (wood p0 walnut)
    (surface-condition p0 smooth)
    (treatment p0 colourfragments)
    (goalsize p0 medium)
    
    
    
    
    (unused p1)
    (goalsize p1 small)
    
    
    
    
    (unused p2)
    (goalsize p2 large)
    
    
    
    
    (available p3)
    (colour p3 blue)
    (wood p3 teak)
    (surface-condition p3 verysmooth)
    (treatment p3 glazed)
    (goalsize p3 large)
    
    
    
    
    (unused p4)
    (goalsize p4 medium)
    
    
    
    
    (unused p5)
    (goalsize p5 small)
    
    
    
    
    (boardsize b0 s3)
    (wood b0 teak)
    (surface-condition b0 rough)
    (available b0)
    (boardsize b1 s4)
    (wood b1 walnut)
    (surface-condition b1 rough)
    (available b1)
  )
  (:goal
    (and
      (available p0)
      (colour p0 black)
      (wood p0 walnut)
      (surface-condition p0 smooth)
      (treatment p0 varnished)
      (available p1)
      (colour p1 green)
      (treatment p1 glazed)
      (available p2)
      (colour p2 natural)
      (treatment p2 glazed)
      (available p3)
      (colour p3 mauve)
      (surface-condition p3 smooth)
      (treatment p3 varnished)
      (available p4)
      (colour p4 blue)
      (wood p4 teak)
      (available p5)
      (surface-condition p5 smooth)
      (treatment p5 glazed)
    )
  )
  
)
