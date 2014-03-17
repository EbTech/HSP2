#!/bin/sh
rm -r Test
mkdir Test

for prob in "6-0" "7-0" "8-0" "9-0" "10-0" "11-0" "12-0" "13-0" "14-0" "14-1" "15-0" "15-1" "16-1" "16-2" "17-0"
do
  echo "	Original Problem	"
  ./bin/hsp2 -v 0 -d forward -h h1eplus -w 1 -e 5 -a bfs -f Test/EG${prob}.eg0 Test/EG${prob}.eg1 examples/blocks/probBLOCKS-${prob}.pddl examples/blocks/domain.pddl
  echo "	Original Problem on EGraph	"
  ./bin/hsp2 -v 0 -d forward -h h1eplus -w 1 -e 5 -a bfs -f Test/EG${prob}.eg1 Test/EG${prob}.eg2 examples/blocks/probBLOCKS-${prob}.pddl examples/blocks/domain.pddl
  echo "	Modified Problem	"
  ./bin/hsp2 -v 0 -d forward -h h1eplus -w 1 -e 5 -a bfs -f Test/EG${prob}.eg0 Test/EG${prob}.trash examples/blocks/probBLOCKS-a${prob}.pddl examples/blocks/domain.pddl
  echo "	Modified Problem on EGraph	"
  ./bin/hsp2 -v 0 -d forward -h h1eplus -w 1 -e 5 -a bfs -f Test/EG${prob}.eg1 Test/EG${prob}.trash examples/blocks/probBLOCKS-a${prob}.pddl examples/blocks/domain.pddl
  echo "--------------------------------------------------------------------------------"
done