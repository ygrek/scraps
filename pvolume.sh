#!/bin/dash

SINK=$(pactl info | grep Default.Sink | awk '{print $3}')
SOURCE=$(pactl info | grep Default.Source | awk '{print $3}')

#echo $SINK
#set -x

case "$1" in
"up") pactl set-sink-mute $SINK 0; pactl set-sink-volume $SINK +5% ;;
"down") pactl set-sink-mute $SINK 0; pactl -- set-sink-volume $SINK -5% ;;
"mute-out") pactl set-sink-mute $SINK toggle ;;
"mute-in") pactl set-source-mute $SOURCE toggle ;;
"next-out")
  OTHER_SINK=$(pactl list sinks | grep Name: | awk '{print $2}' | ~/bin/next.ml.exe "$SINK")
  if [ "$OTHER_SINK" != "$SINK" ]; then
    pactl set-default-sink "$OTHER_SINK"
    notify-send -u normal -i audio-volume-medium-symbolic -t 5000 "Sound output" "$(printf "Now playing on %s" "$OTHER_SINK")"
  fi
  ;;
*) echo unknown command; exit 2;;
esac
