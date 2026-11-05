#!/usr/bin/env python3
"""Drive a Candle REPL with optional DMTCP checkpoint/restore.

usage: cdriver.py [--heap MB] [--log FILE] [--restore CKDIR] [--nohol] item...
  item = file.ml/.hl         -> #use "file";;
         cmd:<ocaml text>     -> sent as is (;; appended if missing)
         ckpt:<name>          -> DMTCP checkpoint into /project/work/ckpt/<name>
Without --restore a fresh Candle is started and hol.ml loaded first (unless
--nohol).  Stops at the first error; exit code 0 iff everything succeeded.
"""
import argparse, os, re, sys, time, glob, shutil, socket, subprocess
import pexpect

CANDLE_ROOT = os.environ.get("CANDLE_ROOT", "/project/repos/candle")
DM = "/project/opt/dmtcp/bin"
CKROOT = "/project/work/ckpt"

PATS = [
    r'\n\- Loading (\S+)',
    r'\n\- Finished loading (\S+)',
    r'\n(ERROR: [^\n]*)',
    r'\n(Parsing failed[^\n]*)',
    r'\n(EXCEPTION: [^\n]*)',
    r'\n(Type error[^\n]*)',
    r'\n# ',
    pexpect.TIMEOUT,
    pexpect.EOF,
]


def free_port():
    s = socket.socket(); s.bind(("", 0)); p = s.getsockname()[1]; s.close()
    return str(p)


def log(msg):
    print(msg, flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--heap", type=int, default=12000)
    ap.add_argument("--stack", type=int, default=0)
    ap.add_argument("--log", default="/project/work/logs/cdriver.log")
    ap.add_argument("--timeout", type=float, default=86400)
    ap.add_argument("--nohol", action="store_true")
    ap.add_argument("--restore", default=None)
    ap.add_argument("--nodmtcp", action="store_true")
    ap.add_argument("--keep", action="store_true",
                    help="do not exit Candle at the end (interactive hand-off)")
    ap.add_argument("items", nargs="*")
    a = ap.parse_args()
    env = dict(os.environ)
    env["CML_HEAP_SIZE"] = str(a.heap)
    if a.stack:
        env["CML_STACK_SIZE"] = str(a.stack)
    logf = open(a.log, "w")
    use_dm = not a.nodmtcp
    port = free_port()
    coord = None
    if use_dm:
        coord = subprocess.Popen([DM + "/dmtcp_coordinator", "--port", port,
                                  "--exit-on-last", "-q", "-q"],
                                 stdout=subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL)
        time.sleep(0.5)
    t0 = time.time()
    sess = os.path.join(CKROOT, "sess_" + port)
    os.makedirs(sess, exist_ok=True)
    if a.restore:
        ck = a.restore if a.restore.startswith("/") else os.path.join(CKROOT, a.restore)
        imgs = sorted(glob.glob(ck + "/ckpt_*.dmtcp"))
        if not imgs:
            log("no checkpoint images in " + ck); return 2
        p = pexpect.spawn(DM + "/dmtcp_restart", ["--coord-port", port, "--ckptdir", sess] + imgs, cwd=CANDLE_ROOT,
                          encoding="utf-8", logfile=logf, timeout=a.timeout,
                          maxread=1 << 20, searchwindowsize=8192)
        time.sleep(2)
        p.sendline('print_string "RESTORED\\n";;')
        p.expect("RESTORED\r?\n", timeout=600)
        p.expect(r'\n# ', timeout=60)
        log("restored %s in %.1fs" % (ck, time.time() - t0))
        items = a.items
    else:
        if use_dm:
            p = pexpect.spawn(DM + "/dmtcp_launch",
                              ["--coord-port", port, "--no-gzip", "--ckptdir", sess,
                               os.path.join(CANDLE_ROOT, "candle.sh")],
                              encoding="utf-8", logfile=logf, cwd=CANDLE_ROOT,
                              env=env, timeout=a.timeout, maxread=1 << 20,
                              searchwindowsize=8192)
        else:
            p = pexpect.spawn(os.path.join(CANDLE_ROOT, "candle.sh"),
                              encoding="utf-8", logfile=logf, cwd=CANDLE_ROOT,
                              env=env, timeout=a.timeout, maxread=1 << 20,
                              searchwindowsize=8192)
        i = p.expect([r'\n# ', pexpect.TIMEOUT, pexpect.EOF], timeout=180)
        if i != 0:
            log("BOOT FAILED"); return 2
        items = ([] if a.nohol else ["hol.ml"]) + a.items
    p.delaybeforesend = None
    for it in items:
        t = time.time()
        if it.startswith("ckpt:"):
            name = it[5:]
            ck = name if name.startswith("/") else os.path.join(CKROOT, name)
            tmp = sess
            for f in glob.glob(sess + "/*"):
                os.remove(f)
            r = subprocess.run([DM + "/dmtcp_command", "--coord-port", port,
                                "--bcheckpoint"],
                               capture_output=True, text=True)
            # make sure the REPL is responsive again
            p.sendline('print_string "CKPTDONE\\n";;')
            p.expect("CKPTDONE\r?\n", timeout=600)
            p.expect(r'\n# ', timeout=60)
            if r.returncode != 0 or not glob.glob(tmp + "/ckpt_*.dmtcp"):
                log("CHECKPOINT FAILED rc=%d %s" % (r.returncode, r.stderr[-300:]))
                return 3
            shutil.rmtree(ck, ignore_errors=True)
            os.makedirs(ck)
            for f in glob.glob(sess + "/ckpt_*.dmtcp"):
                os.rename(f, os.path.join(ck, os.path.basename(f)))
            log("CKPT %-49s %8.1fs  (total %.1fs)" % (ck, time.time() - t, time.time() - t0))
            continue
        if it.startswith("cmd:"):
            cmd = it[4:]
            if not cmd.rstrip().endswith(";;"):
                cmd += ";;"
            label = "cmd " + cmd[:60].replace("\n", " ")
        elif it.startswith("use:"):
            cmd = '#use "%s";;' % it[4:]
            label = it
        else:
            cmd = ('#use "%s";;' if it == "hol.ml" else 'needs "%s";;') % it
            label = it
        p.sendline(cmd)
        stack = []
        err = None
        ctx = ""
        while True:
            k = p.expect(PATS)
            if k == 0:
                stack.append(p.match.group(1))
            elif k == 1:
                f = p.match.group(1)
                if stack and stack[-1] == f:
                    stack.pop()
                if f.startswith("4CT") or f.startswith("Multivariate") or \
                   f.startswith("Autoformalization") or f.startswith("Library") \
                   or f.startswith("4CT_candle"):
                    log("   [%8.1fs] finished %s" % (time.time() - t0, f))
            elif k in (2, 3, 4, 5):
                err = p.match.group(1)
                try:
                    p.expect(r'\n# ', timeout=120)
                    ctx = p.before[-4000:]
                except Exception:
                    ctx = ""
                break
            elif k == 6:
                if not stack:
                    break
            elif k == 7:
                err = "TIMEOUT"; break
            elif k == 8:
                err = "EOF (process died)"
                ctx = p.before[-3000:] if p.before else ""
                break
        dt = time.time() - t
        if err:
            log("FAIL %s after %.1fs: %s" % (label, dt, err))
            log("  while loading: " + " > ".join(stack))
            log("---- context ----\n" + ctx[-3000:])
            p.close(force=True)
            return 1
        log("OK   %-50s %8.1fs  (total %.1fs)" % (label, dt, time.time() - t0))
    if a.keep:
        p.interact()
    p.sendline("exit 0;;")
    p.close(force=True)
    shutil.rmtree(sess, ignore_errors=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
