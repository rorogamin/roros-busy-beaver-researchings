import subprocess

def run_cmd(cmd):
    try:
        out = subprocess.check_output(cmd, shell=True, stderr=subprocess.STDOUT).decode('utf-8')
        print(f"--- {cmd} ---\n" + out)
    except Exception as e:
        print(f"Error {cmd}: {e}")

run_cmd("lscpu | grep -E 'Model name|CPU\(s\):|Thread|L3 cache'")
run_cmd("free -h")
run_cmd("pwd; ls -la")
