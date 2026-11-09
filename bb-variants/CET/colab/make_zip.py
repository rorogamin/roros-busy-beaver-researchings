import zipfile
import os

files_to_zip = [
    'hunt_all_families.cpp',
    'cet3_all_seeds.txt',
    'cet4_all_champions.txt',
    'cet23_seeds_merged.txt',
    'mcet3_all_champions.txt',
    'colab/Catch_Em_Turing_Hunter.ipynb',
    'colab/run_colab.sh'
]

zip_path = 'colab/Catch_Em_Turing_Colab_Bundle.zip'
with zipfile.ZipFile(zip_path, 'w', compression=zipfile.ZIP_DEFLATED) as zf:
    for f in files_to_zip:
        arcname = os.path.basename(f)
        zf.write(f, arcname=arcname)
        print(f"Added {f} as {arcname}")

print(f"\nBundle created at {zip_path} ({os.path.getsize(zip_path)} bytes)")
