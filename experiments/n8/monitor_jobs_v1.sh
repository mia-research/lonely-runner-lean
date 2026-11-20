#!/bin/bash
# monitor_jobs_v1 -- live watch of the session's running jobs: every 60s, one line per job
# (PID, CPU%, CPU-time, RSS, output-file size).  Written to monitor_jobs_v1.log; a job that
# vanishes gets a GONE line.  Usage: monitor_jobs_v1.sh <seconds-to-run>
LOG="/Users/trentpalelei/Desktop/Math Ex/experiments/n8/monitor_jobs_v1.log"
END=$(( $(date +%s) + ${1:-7200} ))
while [ $(date +%s) -lt $END ]; do
  ts=$(date "+%H:%M:%S")
  : >> "$LOG"
  for pat in "perwalk_v1\.py" "v3_chamber_open_v2\.py" "v3_chamber_open_probe_v1\.py" "v3_march_self_v1\.py"; do
    line=$(ps aux | grep -E "${pat}" | grep -v grep | grep -v snapshot-zsh | grep MacOS/Python | head -1)
    if [ -n "$line" ]; then
      pid=$(echo "$line" | awk '{print $2}')
      cpu=$(echo "$line" | awk '{print $3}')
      t=$(echo "$line" | awk '{print $10}')
      rss=$(echo "$line" | awk '{print int($6/1024)"MB"}')
      out=$(echo "$line" | grep -oE "v3_[a-z_]+_v1_[A-Za-z0-9_]*\.out" | head -1)
      sz=0; [ -n "$out" ] && [ -f "/Users/trentpalelei/Desktop/Math Ex/experiments/n8/$out" ] && sz=$(stat -f "%z" "/Users/trentpalelei/Desktop/Math Ex/experiments/n8/$out")
      echo "$ts ALIVE  pid=$pid cpu=${cpu}% time=$t rss=$rss out=$out($sz B)  [$pat]" >> "$LOG"
    else
      echo "$ts GONE   [$pat]" >> "$LOG"
    fi
  done
  sleep 60
done
echo "$(date "+%H:%M:%S") monitor end" >> "$LOG"
