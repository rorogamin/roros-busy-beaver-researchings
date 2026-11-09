// Auto-monitor and pull results from Google Colab A100 triple expedition
const { execSync } = require('child_process');
const fs = require('fs');

console.log('[Colab Monitor] Setting 1-hour watchdog...');

setTimeout(() => {
  try {
    console.log('[Colab Watchdog] 1 hour elapsed! Pulling log and stopping session...');
    execSync('wsl -d Ubuntu -- ~/.local/bin/colab download -s triple-cet-hunt /content/triple_expedition.log ./colab_triple_results.log');
    execSync('wsl -d Ubuntu -- ~/.local/bin/colab stop triple-cet-hunt');
    console.log('[Colab Watchdog] Successfully downloaded colab_triple_results.log and terminated session!');
  } catch (e) {
    console.error('[Colab Watchdog Error]', e.message);
  }
}, 3600 * 1000);
