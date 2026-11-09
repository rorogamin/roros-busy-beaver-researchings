import os

if os.path.exists("/content/colab_hunt.log"):
    with open("/content/colab_hunt.log", "r") as f:
        print(f.read())
else:
    print("Log file not found yet.")
