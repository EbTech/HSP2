#!/bin/sh
rm -r Test
mkdir Test

  echo "	Problem 1	"
  ./bin/hsp2 -v 0 -d forward -h h1emax -w 1 -e 4 -a bfs -f Test/EG${prob}.eg0 Test/EG${prob}.eg1 examples/blocks/probBLOCKS-z1.pddl examples/blocks/domain.pddl
  echo
  echo "	Problem 2	"
  ./bin/hsp2 -v 0 -d forward -h h1emax -w 1 -e 4 -a bfs -f Test/EG${prob}.eg1 Test/EG${prob}.eg2 examples/blocks/probBLOCKS-z2.pddl examples/blocks/domain.pddl
  echo
  echo "	Problem 1 + 2	"
  ./bin/hsp2 -v 0 -d forward -h h1emax -w 1 -e 4 -a bfs -f Test/EG${prob}.eg0 Test/EG${prob}.direct examples/blocks/probBLOCKS-z3.pddl examples/blocks/domain.pddl
  echo
  echo "	Problem 1+2 with egraphs 1 and 2	"
  ./bin/hsp2 -v 0 -d forward -h h1emax -w 1 -e 4 -a bfs -f Test/EG${prob}.eg2 Test/EG${prob}.trash examples/blocks/probBLOCKS-z3.pddl examples/blocks/domain.pddl
  echo
  echo "	Problem 1+2	with egraph 1+2	"
  ./bin/hsp2 -v 0 -d forward -h h1emax -w 1 -e 4 -a bfs -f Test/EG${prob}.direct Test/EG${prob}.trash examples/blocks/probBLOCKS-z3.pddl examples/blocks/domain.pddl
  echo "--------------------------------------------------------------------------------"
