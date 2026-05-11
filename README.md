# Formalizing Analysis of Algorithms, Autumn 2025

https://sites.google.com/view/sorrachai/teaching

## Local installation

This setup process typically takes 1-2 hours. If you have any problems, please reach out to our [TA](mailto:haocheng.wang@inf.ethz.ch) for help. 

1. Install Visual Studio Code and the Lean 4 extension. The instruction can be found [here](https://leanprover-community.github.io/get_started.html#regular-install)
2. Install the following repository on your computer

   https://github.com/sorrachai/FAA2025/

   This can be done by following the same installation step as suggested by [Bhavik's Lean course](https://github.com/b-mehta/formalising-mathematics-notes?tab=readme-ov-file)
   You can replace his repository with  https://github.com/sorrachai/FAA2025/
3. Once you complete step 2, you can navigate to Lecture/Sheet1.lean to check if InfoView is working correctly. During this time, it may compile Mathlib locally (~30 mins on most machines). This happens only once. After that, you can use it normally.

Alternatively, follow the more detailed [installation guide](https://www.notion.so/Lean-4-and-Mathematics-in-Lean-Installation-Guide-26c7fff8cc65809a991fe6631aba0ba3) written by Haocheng. Please use https://github.com/sorrachai/FAA2025/ repository instead of the mathematics-in-lean repository. 

## Important Notice

Lean is not backward compatible. Therefore, please use the same lean version (leanprover/lean4:v4.22.0-rc3 in lean-toolchain) throughout the course. 

## Project organization for coursework

**Create a working copy** to avoid conflicts with repository updates:

```bash
# Inside the FAA2025 folder
cp -r Lectures my_exercises
# Now work in my_exercises/ instead of Lectures/

```
This allows you to:
- Keep original files intact for reference
- Update the repository without losing your work: `git pull && lake exe cache get`
- Submit homework from your personal folder

## Online Editor

You can code Lean using https://live.lean-lang.org/ (simply copying Sheet1.lean), and you can start coding right away. 
