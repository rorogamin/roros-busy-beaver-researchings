// Auto-pull v2 results and terminate A100 session after 10800s
const { execSync } = require('child_process');

console.log('[Watcher v2] Monitoring 3-hour A100 run (session: a100-v2)...');

const startTime = Date.now();

function check() {
  try {
    const elapsedSec = Math.round((Date.now() - startTime) / 1000);
    const psOut = execSync("wsl -d Ubuntu -- bash -c \"echo '!ps aux | grep a100_v2_bin | grep -v grep' > /tmp/ps_check_v2.py && ~/.local/bin/colab exec -s a100-v2 -f /tmp/ps_check_v2.py\"", { encoding: 'utf8', timeout: 30000 });
    
    if (psOut.includes('/content/a100_v2_bin')) {
      console.log(`[Watcher v2 T+${elapsedSec}s] Search running. Checking in 60s...`);
      setTimeout(check, 60000);
    } else {
      console.log('[Watcher v2] 3-Hour Search Finished! Downloading results log...');
      execSync("wsl -d Ubuntu -- bash -c \"~/.local/bin/colab download -s a100-v2 /content/a100_v2_results.log /mnt/c/Users/Rowan/Documents/catch\\ em/a100_v2_results.log\"", { encoding: 'utf8', timeout: 60000 });
      console.log('[Watcher v2] Log saved locally to a100_v2_results.log! Stopping session...');
      execSync("wsl -d Ubuntu -- bash -c \"~/.local/bin/colab stop -s a100-v2\"", { encoding: 'utf8', timeout: 30000 });
      console.log('[Watcher v2] Session terminated cleanly. Compute units protected.');
    }
  } catch (err) {
    console.error('[Watcher v2 error]:', err.message);
    setTimeout(check, 60000);
  }
}

check();
