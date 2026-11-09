// Auto-pull results and terminate A100 Colab session after 7200 seconds
const { execSync } = require('child_process');

console.log('[Watcher] Monitoring A100 2-hour run. Will pull results and stop session upon completion...');

const startTime = Date.now();
const MAX_WAIT_MS = (7200 + 120) * 1000; // 2 hours + 2 min grace

function check() {
  try {
    const elapsedSec = Math.round((Date.now() - startTime) / 1000);
    // Check if process still running
    const psOut = execSync("wsl -d Ubuntu -- bash -c \"echo '!ps aux | grep a100_search_bin | grep -v grep' > /tmp/ps_check.py && ~/.local/bin/colab exec -s a100-cet -f /tmp/ps_check.py\"", { encoding: 'utf8', timeout: 30000 });
    
    if (psOut.includes('/content/a100_search_bin')) {
      console.log(`[Watcher T+${elapsedSec}s] A100 search active. Checking again in 60s...`);
      setTimeout(check, 60000);
    } else {
      console.log('[Watcher] A100 search binary finished! Downloading log...');
      execSync("wsl -d Ubuntu -- bash -c \"~/.local/bin/colab download -s a100-cet /content/a100_results.log /mnt/c/Users/Rowan/Documents/catch\\ em/a100_results.log\"", { encoding: 'utf8', timeout: 60000 });
      console.log('[Watcher] Log saved locally to a100_results.log! Stopping A100 session to save compute units...');
      execSync("wsl -d Ubuntu -- bash -c \"~/.local/bin/colab stop -s a100-cet\"", { encoding: 'utf8', timeout: 30000 });
      console.log('[Watcher] Session stopped cleanly! 0 compute units wasted.');
    }
  } catch (err) {
    console.error('[Watcher error/timeout]:', err.message);
    setTimeout(check, 60000);
  }
}

check();
