#!/usr/bin/env python3

"""A wrapper for cargo that sets up the Prusti environment."""

import sys
if sys.version_info[0] < 3:
    print('You need to run this script with Python 3.')
    sys.exit(1)

import os
import platform
import subprocess
import glob
import csv
import time
import json
import signal
import shutil
import traceback
import datetime

verbose = False
dry_run = False

JAVA_NOT_FOUND_ERR_MSG = """Could not detect a Java installation.
If Java is already installed, you can fix this by setting the JAVA_HOME environment variable."""

RUSTFMT_CRATES = [
    'analysis',
    'prusti',
    #'prusti-common',
    #'prusti-contracts',
    'prusti-contracts-impl',
    'prusti-contracts-internal',
    'prusti-contracts-test',
    #'prusti-interface',
    'prusti-launch',
    'prusti-server',
    #'prusti-specs',
    'prusti-tests',
    'prusti-utils',
    #'prusti-viper',
    'viper',
    'viper-sys',
    'vir',
    'vir-gen',
]

RUSTFMT_PATHS = [
    'prusti-common/src/report/mod.rs',
    'prusti-common/src/utils/mod.rs',
    'prusti-common/src/vir/to_viper.rs',
    'prusti-common/src/vir/low_to_viper/mod.rs',
    'prusti-common/src/vir/optimizations/mod.rs',
    'prusti-interface/src/environment/mir_dump/mod.rs',
    'prusti-interface/src/environment/mir_analyses/mod.rs',
    'prusti-interface/src/environment/mir_sets/mod.rs',
    'prusti-interface/src/environment/mir_body/mod.rs',
    'prusti-interface/src/environment/debug_utils/mod.rs',
    'prusti-tests/tests/verify_partial/**/*.rs',
    'prusti-viper/src/encoder/foldunfold/mod.rs',
    'prusti-viper/src/encoder/mir/mod.rs',
    'prusti-viper/src/encoder/high/mod.rs',
    'prusti-viper/src/encoder/middle/mod.rs',
    'prusti-viper/src/encoder/snapshot/mod.rs',
    'prusti-viper/src/encoder/lifetimes/mod.rs',
    'prusti-viper/src/encoder/definition_collector.rs',
    'vir/defs/high/mod.rs',
    'vir/defs/middle/mod.rs',
    'vir/defs/polymorphic/mod.rs',
    'vir/defs/components/mod.rs',
    'vir/defs/snapshot/mod.rs',
    'vir/defs/low/mod.rs',
]

def default_linux_java_loc():
    if os.path.exists('/usr/lib/jvm/default-java'):
        return '/usr/lib/jvm/default-java'
    elif os.path.exists('/usr/lib/jvm/default'):
        return '/usr/lib/jvm/default'
    elif os.path.exists('/usr/local/sdkman/candidates/java/current'):
        return '/usr/local/sdkman/candidates/java/current'
    report("Could not determine default java location.")


def report(template, *args, **kwargs):
    """Print the message if `verbose` is `True`."""
    if verbose:
        print(template.format(*args, **kwargs))


def error(template, *args, **kwargs):
    """Print the error and exit the program."""
    print(template.format(*args, **kwargs))
    sys.exit(1)


def ensure(condition, err_msg):
    """If `condition` is `False`, print `err_msg` along with a stacktrace, and abort"""
    if not condition:
        traceback.print_stack()
        error(err_msg)


def get_var_or(name, default):
    """If environment variable `name` set, return its value or `default`."""
    if name in os.environ:
        return os.environ[name]
    else:
        return default

def read_json_file(filename):
    with open(filename) as f:
        return json.load(f)

def get_linux_env():
    """Get environment variables for Linux."""
    java_home = get_var_or('JAVA_HOME', default_linux_java_loc())
    ensure(java_home is not None, JAVA_NOT_FOUND_ERR_MSG)
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        ld_library_path = None
        for root, _, files in os.walk(java_home):
            if 'libjvm.so' in files:
                ld_library_path = root
                break
        if ld_library_path is None:
            report("could not find libjvm.so in {}", java_home)
        else:
            variables.append(('LD_LIBRARY_PATH', ld_library_path))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath('viper_tools/server'))
    if not os.path.exists(viper_home):
        viper_home = os.path.abspath('viper_tools/backends')
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    z3_exe = os.path.abspath(os.path.join(viper_home, '../z3/bin/z3'))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    boogie_exe = os.path.abspath(os.path.join(viper_home, '../boogie/Binaries/Boogie'))
    if os.path.exists(boogie_exe):
        variables.append(('BOOGIE_EXE', boogie_exe))
    return variables


def get_mac_env():
    """Get environment variables for Mac."""
    java_home = get_var_or('JAVA_HOME', None)
    if java_home is None:
        java_home = subprocess.run(["/usr/libexec/java_home"], stdout=subprocess.PIPE, encoding="utf8").stdout.strip()
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        ld_library_path = None
        for root, _, files in os.walk(java_home):
            if 'libjli.dylib' in files:
                ld_library_path = root
                break
        if ld_library_path is None:
            report("could not find libjli.dylib in {}", java_home)
        else:
            variables.append(('LD_LIBRARY_PATH', ld_library_path))
            variables.append(('DYLD_LIBRARY_PATH', ld_library_path))
    else:
        error(JAVA_NOT_FOUND_ERR_MSG)
    viper_home = get_var_or('VIPER_HOME', os.path.abspath('viper_tools/server'))
    if not os.path.exists(viper_home):
        viper_home = os.path.abspath('viper_tools/backends')
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    z3_exe = os.path.abspath(os.path.join(viper_home, '../z3/bin/z3'))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    boogie_exe = os.path.abspath(os.path.join(viper_home, '../boogie/Binaries/Boogie'))
    if os.path.exists(boogie_exe):
        variables.append(('BOOGIE_EXE', boogie_exe))
    return variables


def get_win_env():
    """Get environment variables for Windows."""
    java_home = get_var_or('JAVA_HOME', None)
    ensure(java_home is not None, JAVA_NOT_FOUND_ERR_MSG)
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        library_path = None
        for root, _, files in os.walk(java_home):
            if 'jvm.dll' in files:
                library_path = root
                break
        if library_path is None:
            report("could not find jvm.dll in {}", java_home)
        else:
            variables.append(('PATH', library_path))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath(os.path.join('viper_tools', 'server')))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath(os.path.join('viper_tools', 'server')))
    if not os.path.exists(viper_home):
        viper_home = get_var_or('VIPER_HOME', os.path.abspath(os.path.join('viper_tools', 'backends')))
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    else:
        report("could not find VIPER_HOME in {}", viper_home)
    z3_exe = os.path.abspath(os.path.join(viper_home, os.path.join('..', 'z3', 'bin', 'z3.exe')))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    boogie_exe = os.path.abspath(os.path.join(viper_home, '..', 'boogie', 'Binaries', 'Boogie'))
    if os.path.exists(boogie_exe):
        variables.append(('BOOGIE_EXE', boogie_exe))
    return variables


def set_env_variables(env, variables):
    """Set the given environment variables in `env` if not already set, merging special variables."""
    for name, value in variables:
        if name not in env:
            env[name] = value
        elif name in ("PATH", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
            if sys.platform == "win32":
                env[name] += ";" + value
            else:
                env[name] += ":" + value
        report("env: {}={}", name, env[name])


def get_env():
    """Returns the environment with the variables set."""
    env = os.environ.copy()
    if sys.platform in ("linux", "linux2"):
        # Linux
        set_env_variables(env, get_linux_env())
    elif sys.platform == "darwin":
        # Mac
        set_env_variables(env, get_mac_env())
    elif sys.platform == "win32":
        # Windows
        set_env_variables(env, get_win_env())
    else:
        error("unsupported platform: {}", sys.platform)
    return env


def run_command(args, env=None, cwd=None, on_exit=None, report_time=False):
    """Run a command with the given arguments.

    +   ``env`` – an environment in which to run.
    +   ``cwd`` – the path at which to run.
    +   ``on_exit`` – function to be executed on exit.
    +   ``report_time`` – whether to report how long it took to execute
        the command.
    """
    if env is None:
        env = get_env()
    start_time = datetime.datetime.now()
    completed = subprocess.run(args, env=env, cwd=cwd)
    if report_time:
        print(datetime.datetime.now() - start_time)
    if on_exit is not None:
        on_exit()
    if completed.returncode != 0:
        sys.exit(completed.returncode)


def shell(command, term_on_nzec=True):
    """Run a shell command."""
    print("Running a shell command: ", command)
    if not dry_run:
        completed = subprocess.run(command.split())
        if completed.returncode != 0 and term_on_nzec:
            sys.exit(completed.returncode)
        return completed.returncode


def cargo(args):
    """Run cargo with the given arguments."""
    run_command(['cargo'] + args)


def viper_version():
    with open("viper-toolchain", "r") as file:
        return file.read().strip()


def setup_ubuntu():
    """Install the dependencies on Ubuntu."""
    # Install dependencies.
    shell('sudo apt-get update')
    shell('sudo apt-get install -y '
          'build-essential pkg-config '
          'curl gcc libssl-dev')
    # Download Viper.
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsLinux.zip -Lo ViperToolsLinux.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    shell('unzip ViperToolsLinux.zip -d viper_tools')
    os.remove('ViperToolsLinux.zip')


def setup_linux():
    """Install the dependencies on generic Linux."""
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsLinux.zip -Lo ViperToolsLinux.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    shell('unzip ViperToolsLinux.zip -d viper_tools')
    os.remove('ViperToolsLinux.zip')


def setup_mac():
    """Install the dependencies on Mac."""
    # Non-Viper dependencies must be installed manually.
    # Download Viper.
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsMac.zip -Lo ViperToolsMac.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    shell('unzip ViperToolsMac.zip -d viper_tools')
    os.remove('ViperToolsMac.zip')


def setup_win():
    """Install the dependencies on Windows."""
    # Non-Viper dependencies must be installed manually.
    # Download Viper.
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsWin.zip -Lo ViperToolsWin.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    os.mkdir('viper_tools')
    shell('tar -xf ViperToolsWin.zip -C viper_tools')
    os.remove('ViperToolsWin.zip')


def setup_rustup():
    # Update rustup
    shell('rustup self update', term_on_nzec=False)


def setup(args):
    """Install the dependencies."""
    rustup_only = False
    if len(args) == 1 and args[0] == '--dry-run':
        global dry_run
        dry_run = True
    elif len(args) == 1 and args[0] == '--rustup-only':
        rustup_only = True
    elif args:
        error("unexpected arguments: {}", args)
    if not rustup_only:
        if sys.platform in ("linux", "linux2"):
            if 'Ubuntu' in platform.platform():
                setup_ubuntu()
            else:
                setup_linux()
        elif sys.platform == "darwin":
            setup_mac()
        elif sys.platform == "win32":
            setup_win()
        else:
            error("unsupported platform: {}", sys.platform)
    setup_rustup()


def ide(args):
    """Start VS Code with the given arguments."""
    run_command(['code'] + args)

def compare_benchmarks(args):
    def format_runtime(seconds):
        return f"{abs(seconds):.3f}s"
    orig_file = read_json_file("benchmark-output/benchmark1645614279.600768.json")
    new_file = read_json_file("benchmark-output/benchmark1655253113.6554124.json")
    total_diff = 0
    for key in orig_file:
        orig_runtime = orig_file[key][0]
        new_runtime = new_file[key][0]
        diff = orig_runtime - new_runtime
        label = key.removeprefix("prusti-tests/tests/verify/pass/")
        if diff > 0:
            diff_string = f"Decreased by {diff:.3f}s"
        else:
            diff_string = f"Increased by {abs(diff):.3f}s"
        print(f"{label:40}: {format_runtime(orig_runtime):>7} -> {format_runtime(new_runtime):>8} ({diff_string})")
        total_diff += diff
    if total_diff > 0:
        print(f"\nTotal runtime decreased by {total_diff:.3f}s")
    else:
        print(f"\nTotal runtime increased by {abs(total_diff):.3f}s")

def run_benchmarks(args):
    """Run the benchmarks and report the time in a json file"""
    warmup_iterations = 6
    bench_iterations = 3
    warmup_path = "prusti-tests/tests/verify/pass/quick/fibonacci.rs"
    prusti_server_exe = get_prusti_server_path_for_benchmark()
    server_port = "12345"
    output_dir = "benchmark-output"
    benchmark_csv = "benchmarked-files.csv"
    results = {}

    report_name_suffix = ("-" + args[0]) if len(args) > 0 else ''

    env = get_env()
    env['PRUSTI_CHECK_OVERFLOWS'] = 'false' # FIXME: This should not be needed.
    env['PRUSTI_ENABLE_CACHE'] = 'false'
    report("Starting prusti-server ({})", prusti_server_exe)
    server_process = subprocess.Popen([prusti_server_exe,"--port",server_port], env=env)
    time.sleep(2)
    if server_process.poll() != None:
        raise RuntimeError('Could not start prusti-server')

    env["PRUSTI_SERVER_ADDRESS"]="localhost:" + server_port
    try:
        report("Starting warmup of the server")
        for i in range(warmup_iterations):
            t = measure_prusti_time(warmup_path, env)
            report("warmup run {} took {}", i + 1, t)

        report("Finished warmup. Starting benchmark")
        with open(benchmark_csv) as csv_file:
            csv_reader = csv.reader(csv_file, delimiter=',')
            for row in csv_reader:
                file_path = row[0]
                results[file_path] = []
                report("Starting to benchmark {}", file_path)
                for i in range(bench_iterations):
                    t = measure_prusti_time(file_path, env)
                    results[file_path].append(t)
    finally:
        report("terminating prusti-server")
        server_process.send_signal(signal.SIGINT)

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    json_result = json.dumps(results, indent = 2)
    timestamp = time.time()
    output_file = os.path.join(output_dir, "benchmark" + report_name_suffix + str(timestamp) + ".json")
    with open(output_file, "w") as outfile:
        outfile.write(json_result)

    report("Wrote results of benchmark to {}", output_file)


def get_prusti_server_path_for_benchmark():
    project_root_dir = os.path.dirname(os.path.realpath(sys.argv[0]))

    if sys.platform in ("linux", "linux2"):
        return os.path.join(project_root_dir, 'target', 'release', 'prusti-server-driver')
    else:
        error("unsupported platform for benchmarks: {}", sys.platform)


def get_prusti_rustc_path_for_benchmark():
    project_root_dir = os.path.dirname(os.path.realpath(sys.argv[0]))

    if sys.platform in ("linux", "linux2"):
        return os.path.join(project_root_dir, 'target', 'release', 'prusti-rustc')
    else:
        error("unsupported platform for benchmarks: {}", sys.platform)


def measure_prusti_time(input_path, env):
    prusti_rustc_exe = get_prusti_rustc_path_for_benchmark()
    start_time = time.perf_counter()
    run_command([prusti_rustc_exe,"--edition=2018", input_path], env=env)
    end_time = time.perf_counter()
    elapsed = end_time - start_time
    return elapsed



def select_newest_file(paths):
    """Select a file that exists and has the newest modification timestamp."""
    existing_paths = [
        (os.path.getmtime(path), path)
        for path in paths if os.path.exists(path)
    ]
    try:
        return next(reversed(sorted(existing_paths)))[1]
    except:
        error("Could not select the newest file from {}", paths)


def verify_test(args, analyze_quantifiers=False):
    """Runs prusti on the specified files."""
    test = None
    compile_flags = []
    for arg in args:
        if arg.startswith('-'):
            compile_flags.append(arg)
        else:
            if test is None:
                test = arg
            else:
                error("Expected a single argument (test file). Got: {}", args)

    current_path = os.path.abspath(os.path.curdir)
    candidate_prusti_paths = [
        os.path.join(current_path, 'target', 'release', 'prusti-rustc'),
        os.path.join(current_path, 'target', 'debug', 'prusti-rustc')
    ]
    prusti_path = select_newest_file(candidate_prusti_paths)
    report("Selected Prusti: {}", prusti_path)
    if test.startswith('prusti-tests/'):
        test_path = test
    else:
        candidate_test_paths = glob.glob(os.path.join(current_path, "prusti-tests/tests*/*", test))
        if len(candidate_test_paths) == 0:
            error("Not tests found that match: {}", test)
        elif len(candidate_test_paths) > 1:
            error(
                "Expected one test, but found {} tests that match {}. First 5: {}",
                len(candidate_test_paths),
                test,
                candidate_test_paths[:5]
            )
        test_path = candidate_test_paths[0]
    report("Found test: {}", test_path)
    with open(test_path) as fp:
        for line in fp:
            if line.startswith('// compile-flags:'):
                compile_flags.extend(line[len('// compile-flags:'):].strip().split())
        report("Additional compile flags: {}", compile_flags)
    env = get_env()
    if 'prusti-tests/tests/verify_overflow/' in test_path:
        env['PRUSTI_CHECK_OVERFLOWS'] = 'true'
    else:
        env['PRUSTI_CHECK_OVERFLOWS'] = 'false'
    report("env: PRUSTI_CHECK_OVERFLOWS={}", env['PRUSTI_CHECK_OVERFLOWS'])
    os.makedirs('log/config', exist_ok=True)
    env['PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT'] = 'true'
    env['PRUSTI_RUSTC_LOG_ARGS'] = 'log/config/prusti-rustc-args'
    env['PRUSTI_RUSTC_LOG_ENV'] = 'log/config/prusti-rustc-env'
    def verify_test_on_exit():
        generate_launch_json(
            'log/config/prusti-rustc-args',
            'log/config/prusti-rustc-env'
        )
        if analyze_quantifiers:
            analyze_quantifier_logs(test_path)
    run_command(
        [prusti_path, '--edition=2018', test_path] + compile_flags,
        env,
        on_exit=verify_test_on_exit,
        report_time=True,
    )

def generate_launch_json(args_file, env_file):
    """Generates debugging configuration for VS Code extension CodeLLDB.

    https://marketplace.visualstudio.com/items?itemName=vadimcn.vscode-lldb
    """
    with open(args_file) as fp:
        args = fp.read().splitlines()
    with open(env_file) as fp:
        env = dict(
            row.split('=', 1)
            for row in fp.read().splitlines()
        )
    prusti_driver_configuration = {
        "type": "lldb",
        "request": "launch",
        "name": "Debug executable 'prusti-driver'",
        "cargo": {
            "args": [
                "build",
                "--bin=prusti-driver",
                "--package=prusti"
            ],
            "filter": {
                "name": "prusti-driver",
                "kind": "bin"
            }
        },
        "args": args,
        "cwd": "${workspaceFolder}",
        "env": env,
    }
    content = {
        "version": "0.2.0",
        "configurations": [
            prusti_driver_configuration
        ]
    }
    os.makedirs('.vscode', exist_ok=True)
    with open('.vscode/launch.json', 'w') as fp:
        json.dump(content, fp, indent=2)

def analyze_quantifier_logs(test_path):
    qi_explorer = os.path.join('scripts', 'qi_explorer.py')
    if not os.path.exists(qi_explorer):
        shell(
            'curl https://raw.githubusercontent.com/fpoli/qi-explorer/'
            'master/script.py -Lo ' + qi_explorer
        )
    test_file_name = os.path.basename(test_path)
    procedures_dir = os.path.join(
        'log', 'viper_tmp', test_file_name + '*'
    )

    z3_exe = get_env()['Z3_EXE']
    for procedure_dir in sorted(glob.glob(procedures_dir)):
        print("Procedure: ", procedure_dir)
        smt_files = sorted(glob.glob(
            os.path.join(procedure_dir, 'logfile-*.smt2')))
        for smt_file in smt_files:
            print("  Smt file: ", smt_file)
            for line in open(smt_file):
                if line.startswith('; ---------- m_'):
                    print('    method: ', line[13:-12])
            log_folder = os.path.splitext(smt_file)[0]
            os.makedirs(log_folder, exist_ok=True)
            log_file = os.path.join(log_folder, 'qi.log')
            csv_file = os.path.join(log_folder, 'qi.csv')
            svg_file = os.path.join(log_folder, 'qi.svg')
            command = [
                z3_exe,
                'trace=true',
                'trace_file_name=' + log_file,
                'smt.qi.profile=true',
                'smt.qi.profile_freq=10000',
                smt_file
            ]
            with open(os.path.join(log_folder, 'command'), 'w') as fp:
                fp.write(' '.join(command))
            result = subprocess.run(command, capture_output=True)
            with open(os.path.join(log_folder, 'z3.stderr'), 'wb') as fp:
                fp.write(result.stderr)
            with open(os.path.join(log_folder, 'z3.stdout'), 'wb') as fp:
                fp.write(result.stdout)
            subprocess.run([
                'python3', qi_explorer, '--input', log_file,
                '--csv', csv_file, '--svg', svg_file,
            ])

def clippy_in(cwd):
    """Run cargo clippy in given subproject."""
    run_command(['cargo', 'clippy', '--', '-D', 'warnings'], cwd=cwd)

def fmt_in(cwd):
    """Run cargo fmt in given subproject."""
    run_command(['cargo', 'fmt'], cwd=cwd)

def fmt_all():
    """Run rustfmt on all formatted files."""
    for crate in RUSTFMT_CRATES:
        fmt_in(crate)
    for path in RUSTFMT_PATHS:
        for file in glob.glob(path, recursive=True):
            run_command(['rustfmt', file])

def fmt_check_in(cwd):
    """Run cargo fmt check in the given subproject."""
    run_command(['cargo', 'fmt', '--', '--check'], cwd=cwd)

def fmt_check_all():
    """Run rustfmt check on all formatted files."""
    for crate in RUSTFMT_CRATES:
        fmt_check_in(crate)
    for path in RUSTFMT_PATHS:
        for file in glob.glob(path, recursive=True):
            run_command(['rustfmt', '--check', file])

def main(argv):
    global verbose
    analyze_quantifiers = False
    for i, arg in enumerate(argv):
        if arg.startswith('+'):
            if arg == '+v' or arg == '++verbose':
                verbose = True
                continue
            elif arg == '++analyze-quantifiers':
                analyze_quantifiers = True
                continue
            else:
                error('unknown option: {}', arg)
        elif arg == 'setup':
            setup(argv[i+1:])
            break
        elif arg == 'ide':
            ide(argv[i+1:])
            break
        elif arg == 'run-benchmarks':
            run_benchmarks(argv[i+1:])
            break
        elif arg == 'compare-benchmarks':
            compare_benchmarks(argv[i+1:])
            break
        elif arg == 'verify-test':
            verify_test(argv[i+1:], analyze_quantifiers=analyze_quantifiers)
            break
        elif arg == 'exec':
            run_command(argv[i+1:])
            break
        elif arg == 'clippy-in':
            clippy_in(*argv[i+1:])
            break
        elif arg == 'fmt-check':
            fmt_check_in(*argv[i+1:])
            break
        elif arg == 'fmt-check-all':
            fmt_check_all(*argv[i+1:])
            break
        elif arg == 'fmt':
            fmt_in(*argv[i+1:])
            break
        elif arg == 'fmt-all':
            fmt_all(*argv[i+1:])
            break
        else:
            cargo(argv[i:])
            break
    if not argv:
        cargo(argv)


if __name__ == '__main__':
    main(sys.argv[1:])
