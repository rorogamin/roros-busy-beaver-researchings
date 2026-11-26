#!/usr/bin/env bash
# p sweep: start from the landmark configuration with 5^p, see which halt and when.
cd "$(dirname "$0")" || exit 1
M="0LD3LB5LD2RA4LB5RD_1RZ3RB1LC2RA3RB4LC_3RB1LB3LC2RC4LC3LA_1RA1LD0LD4RA2LD2LC"
: > psweep.log
for p in 0 1 2 3 4 5 6 7 8 9 10 11 12; do
  (
    r=$(./bstart.exe "$M" "0^inf 3^(1) 2^5 A> 1 4 5^$p 0^inf" 2000000000 | head -1)
    printf "p=%s %s\n" "$p" "$r" >> psweep.log
  ) &
done
wait
echo "PSWEEP DONE" >> psweep.log
