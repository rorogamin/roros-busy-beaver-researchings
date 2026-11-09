import subprocess

try:
    p = subprocess.Popen(["/content/hunt_all_families", "8"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    import time
    time.sleep(3)
    out = ""
    # read available lines
    import fcntl, os
    fl = fcntl.fcntl(p.stdout.fileno(), fcntl.F_GETFL)
    fcntl.fcntl(p.stdout.fileno(), fcntl.F_SETFL, fl | os.O_NONBLOCK)
    try:
        out = p.stdout.read()
    except Exception as e:
        out = str(e)
    ret = p.poll()
    print("Process returncode after 3s:", ret)
    print("Output:\n", out)
    if ret is None:
        p.terminate()
except Exception as e:
    print("Error:", e)
