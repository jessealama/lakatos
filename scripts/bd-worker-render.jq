# Render one claude -p stream-json event as a terminal line, or nothing.
# Input is raw lines (jq -R): non-JSON lines from stderr noise are dropped.
# The full stream goes to the log file untouched; this is the live view.
# Every output line is prefixed with the `prefix` named argument
# ("[role] [bead]") when one is given, the final result's summary lines
# included; without it the lines are bare, so an older caller still works.

def short($n): tostring | gsub("\\s+"; " ") | .[0:$n];
def stamp: now | strflocaltime("%H:%M");

(fromjson? // empty |
if .type == "assistant" then
  (.message.content // [])[]? |
  if .type == "tool_use" then
    "\(stamp) ▶ \(.name) " + (
      if .name == "Bash" then (.input.description // .input.command | short(140))
      elif .input.file_path? then (.input.file_path | short(140))
      elif .input.pattern? then (.input.pattern | short(140))
      elif .input.prompt? then (.input.prompt | short(140))
      elif .input.description? then (.input.description | short(140))
      else (.input | short(140)) end)
  elif .type == "text" then "\(stamp) 💬 " + (.text | short(220))
  else empty end
elif .type == "user" then
  (.message.content // [])[]? | select(.type == "tool_result" and .is_error == true) |
  "\(stamp) ✗ tool error: " + (.content | short(220))
elif .type == "result" then
  "\(stamp) ■ \(.subtype): \(.num_turns) turns, \((.duration_ms // 0) / 60000 | floor) min, $\((.total_cost_usd // 0) * 100 | round / 100)\n" + (.result // "")
else empty end)
| ($ARGS.named.prefix // "") as $prefix
| split("\n") | map(if $prefix == "" then . else $prefix + " " + . end) | join("\n")
