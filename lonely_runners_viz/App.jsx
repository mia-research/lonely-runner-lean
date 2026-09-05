import { useState, useEffect, useRef } from "react";

const TAU = 2 * Math.PI;
const N = 11;
const THRESHOLD = 1 / N;           // ≈ 0.0909 — loneliness gap
const NEAR_THRESHOLD = 0.075;      // slow-mo kicks in below this gap

const allSpeeds = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
const movingSpeeds = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

const MUTED = "#3e4555";
const LONELY_COL = "#2ecc71";
const CLOSE_COL = "#5a3a3a";
const TRACK_BG = "#131620";

function frac(x) { return ((x % 1) + 1) % 1; }
function dist(x) { const f = frac(x); return Math.min(f, 1 - f); }

// Minimum circular distance from runner s to any other runner at time t
function minDistToOthers(s, t) {
  let min = Infinity;
  for (const o of allSpeeds) {
    if (o === s) continue;
    min = Math.min(min, dist((o - s) * t));
  }
  return min;
}

function isRunnerLonely(s, time) {
  return minDistToOthers(s, time) >= THRESHOLD;
}

export default function App() {
  const [time, setTime] = useState(0);
  const [playing, setPlaying] = useState(true);
  const [baseSpeed, setBaseSpeed] = useState(0.06);
  const [autoSlow, setAutoSlow] = useState(true);
  const [firstLonely, setFirstLonely] = useState(() =>
    Object.fromEntries(allSpeeds.map(s => [s, null]))
  );
  const [lonelyFlash, setLonelyFlash] = useState(null);
  const [screenFlash, setScreenFlash] = useState(null);
  const lastTimeRef = useRef(performance.now());
  const frameRef = useRef();
  const flashTimer = useRef(null);
  const screenTimer = useRef(null);

  const positions = movingSpeeds.map(s => frac(s * time));

  // Per-runner minimum gap to any other runner (fixed: was wrongly dist(s*time))
  const distances = movingSpeeds.map(s => minDistToOthers(s, time));

  // Include runner 0 in the global min-gap calculation
  const dist0 = minDistToOthers(0, time);
  const globalMinDist = Math.min(dist0, ...distances);

  const lonelyNow = {};
  for (const s of allSpeeds) lonelyNow[s] = isRunnerLonely(s, time);

  // Detect first-lonely events
  useEffect(() => {
    if (time < 0.001) return;
    let updated = false;
    const next = { ...firstLonely };
    for (const s of allSpeeds) {
      if (lonelyNow[s] && firstLonely[s] === null) {
        next[s] = time;
        updated = true;
        setLonelyFlash(s);
        clearTimeout(flashTimer.current);
        flashTimer.current = setTimeout(() => setLonelyFlash(null), 600);
        setScreenFlash(true);
        clearTimeout(screenTimer.current);
        screenTimer.current = setTimeout(() => setScreenFlash(false), 250);
      }
    }
    if (updated) setFirstLonely(next);
  }, [time]);

  // Slow-mo: engage when ANY runner's gap exceeds NEAR_THRESHOLD (approaching lonely)
  // Uses corrected distances; also checks runner 0
  const nearLonely =
    dist0 > NEAR_THRESHOLD ||
    distances.some(d => d > NEAR_THRESHOLD);

  const slowFactor = (autoSlow && nearLonely) ? 0.25 : 1;

  useEffect(() => {
    if (!playing) return;
    const tick = (now) => {
      const dt = (now - lastTimeRef.current) / 1000;
      lastTimeRef.current = now;
      setTime(t => t + dt * baseSpeed * slowFactor);
      frameRef.current = requestAnimationFrame(tick);
    };
    lastTimeRef.current = performance.now();
    frameRef.current = requestAnimationFrame(tick);
    return () => cancelAnimationFrame(frameRef.current);
  }, [playing, baseSpeed, slowFactor]);

  const W = 500, H = 500;
  const cx = W / 2, cy = H / 2, R = 195;

  function angleOf(pos) { return pos * TAU - TAU / 4; }
  function ptOn(pos, r) {
    const a = angleOf(pos);
    return [cx + r * Math.cos(a), cy + r * Math.sin(a)];
  }
  function dangerArc() {
    const a1 = angleOf(1 - THRESHOLD);
    const a2 = angleOf(THRESHOLD);
    return `M ${cx + R * Math.cos(a1)} ${cy + R * Math.sin(a1)} A ${R} ${R} 0 0 1 ${cx + R * Math.cos(a2)} ${cy + R * Math.sin(a2)}`;
  }

  const solvedCount = allSpeeds.filter(s => firstLonely[s] !== null).length;
  const gapPct = Math.round(globalMinDist / THRESHOLD * 100);

  return (
    <div style={{
      minHeight: "100vh", background: "#08090e",
      fontFamily: "'Inter', -apple-system, sans-serif",
      color: "#e2e8f0", display: "flex", flexDirection: "column",
      alignItems: "center", padding: "20px 16px",
    }}>
      <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=JetBrains+Mono:wght@400;600&display=swap" rel="stylesheet" />
      <style>{`
        @keyframes ringBurst {
          0%  { r: ${R - 10}; opacity: 0.8; stroke-width: 5; }
          100% { r: ${R + 45}; opacity: 0; stroke-width: 1; }
        }
        @keyframes lonelyPulse {
          0%, 100% { opacity: 0.6; }
          50%       { opacity: 1; }
        }
      `}</style>

      <h1 style={{ fontSize: 20, fontWeight: 700, margin: "0 0 2px 0", letterSpacing: 0.5, color: "#94a3b8" }}>
        Eleven Lonely Runners
      </h1>
      <p style={{ fontSize: 11, color: "#475569", margin: "0 0 16px 0",
        fontFamily: "'JetBrains Mono', monospace" }}>
        every runner eventually gets lonely
      </p>

      <div style={{ display: "flex", gap: 20, alignItems: "flex-start", flexWrap: "wrap",
        justifyContent: "center" }}>

        {/* ── Circle ── */}
        <div style={{ position: "relative" }}>
          <svg width={W} height={H} style={{ display: "block" }}>
            <defs>
              <filter id="glow"><feGaussianBlur stdDeviation="4" /></filter>
              <filter id="bigglow"><feGaussianBlur stdDeviation="12" /></filter>
            </defs>

            {/* Screen flash */}
            {screenFlash && (
              <circle cx={cx} cy={cy} r={R + 60} fill={LONELY_COL} opacity={0.12} />
            )}

            {/* Ring burst on new lonely */}
            {screenFlash && (
              <circle cx={cx} cy={cy} fill="none" stroke={LONELY_COL}
                style={{ animation: "ringBurst 0.45s ease-out forwards" }} />
            )}

            {/* Track */}
            <circle cx={cx} cy={cy} r={R} fill="none" stroke="#1a1e2a" strokeWidth={28} />
            <circle cx={cx} cy={cy} r={R} fill="none" stroke="#252a38" strokeWidth={1} />

            {/* Danger zone */}
            <path d={dangerArc()} fill="none" stroke="#ff000018" strokeWidth={26} strokeLinecap="round" />

            {/* Origin — runner 0 */}
            {(() => {
              const [ox, oy] = ptOn(0, R);
              const lonely = lonelyNow[0];
              const flashing = lonelyFlash === 0;
              const tooClose = dist0 < THRESHOLD;
              return (
                <g>
                  {lonely && (
                    <circle cx={ox} cy={oy} r={20} fill={LONELY_COL}
                      opacity={flashing ? 0.5 : 0.15} filter="url(#glow)" />
                  )}
                  <circle cx={ox} cy={oy} r={10}
                    fill={lonely ? LONELY_COL : tooClose ? CLOSE_COL : TRACK_BG}
                    stroke={lonely ? LONELY_COL : MUTED} strokeWidth={2}
                    style={{ transition: "fill 0.08s" }} />
                  <text x={ox} y={oy + 1} textAnchor="middle" dominantBaseline="middle"
                    fill={lonely ? "#000" : MUTED} fontSize={9} fontWeight={700}
                    fontFamily="'JetBrains Mono', monospace">0</text>
                </g>
              );
            })()}

            {/* Moving runners */}
            {movingSpeeds.map((s, i) => {
              const [x, y] = ptOn(positions[i], R);
              const lonely = lonelyNow[s];
              const flashing = lonelyFlash === s;
              const tooClose = distances[i] < THRESHOLD;   // now uses correct min-gap
              return (
                <g key={s}>
                  {lonely && (
                    <circle cx={x} cy={y} r={flashing ? 26 : 18}
                      fill={LONELY_COL} opacity={flashing ? 0.5 : 0.15}
                      filter="url(#glow)"
                      style={{ transition: "r 0.2s, opacity 0.2s" }} />
                  )}
                  <circle cx={x} cy={y} r={8}
                    fill={lonely ? LONELY_COL : tooClose ? CLOSE_COL : MUTED}
                    stroke={lonely ? LONELY_COL : "none"} strokeWidth={lonely ? 2 : 0}
                    style={{ transition: "fill 0.08s" }} />
                  <text x={x} y={y + 1} textAnchor="middle" dominantBaseline="middle"
                    fill={lonely ? "#000" : "#0a0b11"} fontSize={8} fontWeight={700}
                    fontFamily="'JetBrains Mono', monospace"
                    opacity={lonely ? 1 : 0.6}>{s}</text>
                </g>
              );
            })}

            {/* Centre info */}
            <text x={cx} y={cy - 12} textAnchor="middle"
              fill={solvedCount === 11 ? LONELY_COL : "#475569"} fontSize={18} fontWeight={700}
              fontFamily="'JetBrains Mono', monospace">
              {solvedCount}/11
            </text>
            <text x={cx} y={cy + 8} textAnchor="middle" fill="#333a48" fontSize={9}
              fontFamily="'JetBrains Mono', monospace">
              proven lonely
            </text>

            {/* Live gap meter */}
            <text x={cx} y={cy + 24} textAnchor="middle"
              fill={gapPct >= 100 ? LONELY_COL : gapPct > 80 ? "#f39c12" : "#333a48"}
              fontSize={9} fontFamily="'JetBrains Mono', monospace">
              gap {gapPct}%
            </text>

            {autoSlow && slowFactor < 0.9 && playing && (
              <text x={cx} y={cy + 38} textAnchor="middle" fill="#6b5b1b" fontSize={8}
                fontFamily="'JetBrains Mono', monospace" opacity={0.7}>
                slow-mo
              </text>
            )}
          </svg>
        </div>

        {/* ── Side panel ── */}
        <div style={{ width: 220, display: "flex", flexDirection: "column", gap: 10 }}>

          {/* Controls */}
          <div style={panel}>
            <div style={{ display: "flex", gap: 6, marginBottom: 6 }}>
              <button onClick={() => setPlaying(p => !p)} style={btn}>
                {playing ? "⏸" : "▶"}
              </button>
              <button onClick={() => {
                setTime(0);
                setFirstLonely(Object.fromEntries(allSpeeds.map(s => [s, null])));
              }} style={btn}>↺</button>
              <button onClick={() => setBaseSpeed(s => Math.max(0.01, s * 0.5))} style={btn}>½×</button>
              <button onClick={() => setBaseSpeed(s => Math.min(0.5, s * 2))} style={btn}>2×</button>
            </div>
            <label style={toggleRow}>
              <input type="checkbox" checked={autoSlow} onChange={e => setAutoSlow(e.target.checked)}
                style={{ accentColor: "#f39c12" }} />
              <span>Slow-mo near lonely</span>
            </label>
            <div style={{ fontSize: 10, color: "#333a48", fontFamily: "'JetBrains Mono', monospace" }}>
              t = {time.toFixed(3)}
            </div>
          </div>

          {/* Scoreboard */}
          <div style={panel}>
            <div style={{ fontSize: 10, fontWeight: 600, color: "#475569", marginBottom: 8,
              fontFamily: "'JetBrains Mono', monospace", textTransform: "uppercase",
              letterSpacing: 1 }}>Scoreboard</div>
            <div style={{ display: "grid", gridTemplateColumns: "repeat(4, 1fr)", gap: 5 }}>
              {allSpeeds.map(s => {
                const solved = firstLonely[s] !== null;
                const flashing = lonelyFlash === s;
                const lonelyRn = lonelyNow[s];
                // Three distinct visual states:
                //  flashing  → just became lonely (bright pop)
                //  lonelyRn  → currently lonely (solid bright border)
                //  solved    → was lonely before (dim green tint)
                //  none      → not yet seen lonely
                const bg = flashing ? "#2ecc7130"
                  : lonelyRn ? "#2ecc7120"
                  : solved   ? "#2ecc7108"
                  : "#0c0d14";
                const border = flashing ? LONELY_COL
                  : lonelyRn ? LONELY_COL
                  : solved   ? "#2ecc7144"
                  : "#181c28";
                return (
                  <div key={s} style={{
                    textAlign: "center", padding: "6px 2px", borderRadius: 8,
                    background: bg,
                    border: `1.5px solid ${border}`,
                    transition: "all 0.12s",
                    boxShadow: lonelyRn ? `0 0 6px ${LONELY_COL}44` : "none",
                  }}>
                    <div style={{
                      fontSize: 15, fontWeight: 700,
                      color: lonelyRn ? LONELY_COL : solved ? "#2ecc7166" : "#2a2f3d",
                      fontFamily: "'JetBrains Mono', monospace",
                      transition: "color 0.12s",
                    }}>{s}</div>
                    <div style={{
                      fontSize: 7, marginTop: 1,
                      color: solved ? "#2ecc7188" : "#1e2230",
                      fontFamily: "'JetBrains Mono', monospace",
                    }}>
                      {solved ? `t=${firstLonely[s].toFixed(2)}` : "—"}
                    </div>
                  </div>
                );
              })}
            </div>
            {solvedCount === 11 && (
              <div style={{ marginTop: 8, textAlign: "center", fontSize: 11, fontWeight: 600,
                color: LONELY_COL, fontFamily: "'JetBrains Mono', monospace" }}>
                ✓ all runners proven lonely
              </div>
            )}
          </div>

          {/* Legend */}
          <div style={{ ...panel, borderColor: "#141820" }}>
            <div style={{ fontSize: 10, color: "#3e4555", lineHeight: 1.7 }}>
              <span style={{ color: LONELY_COL }}>Green</span> = lonely now (gap ≥ 1/11)<br />
              <span style={{ color: CLOSE_COL, background: CLOSE_COL, borderRadius: 3, padding: "0 4px" }}>■</span>{" "}
              <span style={{ color: "#4a3030" }}>Dark</span> = crowded (gap &lt; 1/11)<br />
              Scoreboard: bright border = lonely <em>right now</em>; dim = was lonely before.
            </div>
          </div>

          {/* Explanation */}
          <div style={{ ...panel, borderColor: "#141820" }}>
            <div style={{ fontSize: 11, color: "#3e4555", lineHeight: 1.6 }}>
              Runners sit dark until they achieve ≥ 1/11 separation from
              every other runner. The conjecture says all eleven must eventually
              light up.
            </div>
          </div>
        </div>
      </div>

      <div style={{ marginTop: 16, fontSize: 9, color: "#1e2230",
        fontFamily: "'JetBrains Mono', monospace" }}>
        T. Palelei — MI Research Foundation — 2026
      </div>
    </div>
  );
}

const panel = {
  background: "#0c0d14", borderRadius: 10, border: "1px solid #181c28", padding: 10,
};
const btn = {
  background: "#141820", border: "1px solid #1e2430", color: "#64748b",
  padding: "5px 11px", borderRadius: 7, cursor: "pointer", fontSize: 13,
  fontFamily: "'JetBrains Mono', monospace",
};
const toggleRow = {
  display: "flex", alignItems: "center", gap: 8, marginBottom: 4,
  fontSize: 11, color: "#475569", cursor: "pointer",
  fontFamily: "'JetBrains Mono', monospace",
};
