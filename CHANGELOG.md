## WIP


## Version 0.1: start of assignment

* First code.
* ================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 0 items / 2 errors

======================================================= ERRORS ========================================================
________________________________________ ERROR collecting tests/test_labunc.py ________________________________________
ImportError while importing test module 'C:\Users\ct347\ci-exercise\tests\test_labunc.py'.
Hint: make sure your test modules/packages have valid Python names.
Traceback:
..\AppData\Local\Programs\Python\Python311\Lib\importlib\__init__.py:126: in import_module
    return _bootstrap._gcd_import(name[level:], package, level)
tests\test_labunc.py:1: in <module>
    from unc import LabUnc
E   ModuleNotFoundError: No module named 'unc'
________________________________________ ERROR collecting tests/test_stdunc.py ________________________________________
ImportError while importing test module 'C:\Users\ct347\ci-exercise\tests\test_stdunc.py'.
Hint: make sure your test modules/packages have valid Python names.
Traceback:
..\AppData\Local\Programs\Python\Python311\Lib\importlib\__init__.py:126: in import_module
    return _bootstrap._gcd_import(name[level:], package, level)
tests\test_stdunc.py:1: in <module>
    from unc import StdUnc
E   ModuleNotFoundError: No module named 'unc'
=============================================== short test summary info ===============================================
ERROR tests/test_labunc.py
ERROR tests/test_stdunc.py
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! Interrupted: 2 errors during collection !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
================================================== 2 errors in 0.09s ==================================================
nox > Command pytest  failed with exit code 2
nox > Session tests failed.
nox > Running session lint
nox > Creating virtual environment (virtualenv) using python.exe in .nox\lint
nox > python -m pip install pre-commit
nox > pre-commit run -a
trim trailing whitespace.................................................Failed
- hook id: trailing-whitespace
- exit code: 1
- files were modified by this hook

Fixing pyproject.toml
Fixing noxfile.py

check for added large files..............................................Passed
check for case conflicts.................................................Passed
check for merge conflicts................................................Passed
check for broken symlinks............................(no files to check)Skipped
check yaml...............................................................Passed
debug statements (python)................................................Passed
fix end of files.........................................................Failed
- hook id: end-of-file-fixer
- exit code: 1
- files were modified by this hook

Fixing noxfile.py

mixed line ending........................................................Passed
fix requirements.txt.................................(no files to check)Skipped
ruff.....................................................................Passed
ruff-format..............................................................Failed
- hook id: ruff-format
- files were modified by this hook

1 file reformatted, 3 files left unchanged

nox > Command pre-commit run -a failed with exit code 1
nox > Session lint failed.
nox > Ran multiple sessions:
nox > * tests: failed
nox > * lint: failed
PS C:\Users\ct347\ci-exercise>
PS C:\Users\ct347\ci-exercise>
PS C:\Users\ct347\ci-exercise>
PS C:\Users\ct347\ci-exercise> nox
nox > Running session tests
nox > Creating virtual environment (virtualenv) using python.exe in .nox\tests
nox > python -m pip install '-e.[test]'
nox > pytest
================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 85 items

tests\test_labunc.py .....                                                                                       [  5%]
tests\test_stdunc.py ................................................................................            [100%]

================================================= 85 passed in 0.12s ==================================================
nox > Session tests was successful.
nox > Running session lint
nox > Creating virtual environment (virtualenv) using python.exe in .nox\lint
nox > python -m pip install pre-commit
nox > pre-commit run -a
trim trailing whitespace.................................................Failed
- hook id: trailing-whitespace
- exit code: 1
- files were modified by this hook

Fixing pyproject.toml

check for added large files..............................................Passed
check for case conflicts.................................................Passed
check for merge conflicts................................................Passed
check for broken symlinks............................(no files to check)Skipped
check yaml...............................................................Passed
debug statements (python)................................................Passed
fix end of files.........................................................Passed
mixed line ending........................................................Passed
fix requirements.txt.................................(no files to check)Skipped
ruff.....................................................................Passed
ruff-format..............................................................Passed
nox > Command pre-commit run -a failed with exit code 1
nox > Session lint failed.
nox > Ran multiple sessions:
nox > * tests: success
nox > * lint: failed
PS C:\Users\ct347\ci-exercise> nox
nox > Running session tests
nox > Creating virtual environment (virtualenv) using python.exe in .nox\tests
nox > python -m pip install '-e.[test]'
nox > pytest
================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 85 items

tests\test_labunc.py .....                                                                                       [  5%]
tests\test_stdunc.py ................................................................................            [100%]

================================================= 85 passed in 0.11s ==================================================
nox > Session tests was successful.
nox > Running session lint
nox > Creating virtual environment (virtualenv) using python.exe in .nox\lint
nox > python -m pip install pre-commit
nox > pre-commit run -a
An error has occurred: InvalidConfigError:
==> File .pre-commit-config.yaml
=====> while scanning a simple key
  in "<unicode string>", line 41, column 9
could not find expected ':'
  in "<unicode string>", line 43, column 7
Check the log at C:\Users\ct347\.cache\pre-commit\pre-commit.log
nox > Command pre-commit run -a failed with exit code 1
nox > Session lint failed.
nox > Ran multiple sessions:
nox > * tests: success
nox > * lint: failed
PS C:\Users\ct347\ci-exercise> nox
nox > Running session tests
nox > Creating virtual environment (virtualenv) using python.exe in .nox\tests
nox > python -m pip install '-e.[test]'
nox > pytest
================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 85 items

tests\test_labunc.py .....                                                                                       [  5%]
tests\test_stdunc.py ................................................................................            [100%]

================================================= 85 passed in 0.11s ==================================================
nox > Session tests was successful.
nox > Running session lint
nox > Creating virtual environment (virtualenv) using python.exe in .nox\lint
nox > python -m pip install pre-commit
nox > pre-commit run -a
An error has occurred: InvalidConfigError:
==> File .pre-commit-config.yaml
=====> while scanning a simple key
  in "<unicode string>", line 41, column 9
could not find expected ':'
  in "<unicode string>", line 43, column 7
Check the log at C:\Users\ct347\.cache\pre-commit\pre-commit.log
nox > Command pre-commit run -a failed with exit code 1
nox > Session lint failed.
nox > Ran multiple sessions:
nox > * tests: success
nox > * lint: failed
PS C:\Users\ct347\ci-exercise> nox
nox > Running session tests
nox > Creating virtual environment (virtualenv) using python.exe in .nox\tests
nox > python -m pip install '-e.[test]'
nox > pytest
================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 85 items

tests\test_labunc.py .....                                                                                       [  5%]
tests\test_stdunc.py ................................................................................            [100%]

================================================= 85 passed in 0.10s ==================================================
nox > Session tests was successful.
nox > Running session lint
nox > Creating virtual environment (virtualenv) using python.exe in .nox\lint
nox > python -m pip install pre-commit
nox > pre-commit run -a
An error has occurred: InvalidConfigError:
==> File .pre-commit-config.yaml
=====> while scanning a simple key
  in "<unicode string>", line 41, column 9
could not find expected ':'
  in "<unicode string>", line 43, column 7
Check the log at C:\Users\ct347\.cache\pre-commit\pre-commit.log
nox > Command pre-commit run -a failed with exit code 1
nox > Session lint failed.
nox > Ran multiple sessions:
nox > * tests: success
nox > * lint: failed
PS C:\Users\ct347\ci-exercise> nox -R
nox > Running session tests
nox > Re-using existing virtual environment at .nox\tests.
nox > pytest
================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 85 items

tests\test_labunc.py .....                                                                                       [  5%]
tests\test_stdunc.py ................................................................................            [100%]

================================================= 85 passed in 0.12s ==================================================
nox > Session tests was successful.
nox > Running session lint
nox > Re-using existing virtual environment at .nox\lint.
nox > pre-commit run -a
trim trailing whitespace.................................................Failed
- hook id: trailing-whitespace
- exit code: 1
- files were modified by this hook

Fixing .pre-commit-config.yaml

check for added large files..............................................Passed
check for case conflicts.................................................Passed
check for merge conflicts................................................Passed
check for broken symlinks............................(no files to check)Skipped
check yaml...............................................................Passed
debug statements (python)................................................Passed
fix end of files.........................................................Failed
- hook id: end-of-file-fixer
- exit code: 1
- files were modified by this hook

Fixing .pre-commit-config.yaml

mixed line ending........................................................Passed
fix requirements.txt.................................(no files to check)Skipped
ruff.....................................................................Passed
ruff-format..............................................................Passed
nox > Command pre-commit run -a failed with exit code 1
nox > Session lint failed.
nox > Ran multiple sessions:
nox > * tests: success
nox > * lint: failed
PS C:\Users\ct347\ci-exercise> nox -R
nox > Running session tests
nox > Re-using existing virtual environment at .nox\tests.
nox > pytest
================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 85 items

tests\test_labunc.py .....                                                                                       [  5%]
tests\test_stdunc.py ................................................................................            [100%]

================================================= 85 passed in 0.11s ==================================================
nox > Session tests was successful.
nox > Running session lint
nox > Re-using existing virtual environment at .nox\lint.
nox > pre-commit run -a
trim trailing whitespace.................................................Failed
- hook id: trailing-whitespace
- exit code: 1
- files were modified by this hook

Fixing .pre-commit-config.yaml

check for added large files..............................................Passed
check for case conflicts.................................................Passed
check for merge conflicts................................................Passed
check for broken symlinks............................(no files to check)Skipped
check yaml...............................................................Passed
debug statements (python)................................................Passed
fix end of files.........................................................Failed
- hook id: end-of-file-fixer
- exit code: 1
- files were modified by this hook

Fixing .pre-commit-config.yaml

mixed line ending........................................................Passed
fix requirements.txt.................................(no files to check)Skipped
ruff.....................................................................Passed
ruff-format..............................................................Passed
nox > Command pre-commit run -a failed with exit code 1
nox > Session lint failed.
nox > Ran multiple sessions:
nox > * tests: success
nox > * lint: failed
PS C:\Users\ct347\ci-exercise> nox -R
nox > Running session tests
nox > Re-using existing virtual environment at .nox\tests.
nox > pytest
================================================= test session starts =================================================
platform win32 -- Python 3.11.6, pytest-7.4.3, pluggy-1.3.0
rootdir: C:\Users\ct347\ci-exercise
configfile: pyproject.toml
testpaths: tests
collected 85 items

tests\test_labunc.py .....                                                                                       [  5%]
tests\test_stdunc.py ................................................................................            [100%]

================================================= 85 passed in 0.12s ==================================================
nox > Session tests was successful.
nox > Running session lint
nox > Re-using existing virtual environment at .nox\lint.
nox > pre-commit run -a
trim trailing whitespace.................................................Passed
check for added large files..............................................Passed
check for case conflicts.................................................Passed
check for merge conflicts................................................Passed
check for broken symlinks............................(no files to check)Skipped
check yaml...............................................................Passed
debug statements (python)................................................Passed
fix end of files.........................................................Passed
mixed line ending........................................................Passed
fix requirements.txt.................................(no files to check)Skipped
ruff.....................................................................Passed
ruff-format..............................................................Passed
nox > Session lint was successful.
nox > Ran multiple sessions:
nox > * tests: success
nox > * lint: success
