"""Prepare an isolated browser fixture; optionally run it using CHROME_BIN.

python test/test_revolver_browser.py prepares .tools/revolver-fixture/index.html.
CHROME_BIN=/path/to/chrome python test/test_revolver_browser.py --run executes it.
No installed browser automation framework is required.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
def prepare():
    out=ROOT/'.tools/revolver-fixture';out.mkdir(parents=True,exist_ok=True)
    entries=[dict(title=f'Result {i}',label=f'thm:result-{i}',url='index.html#target',kind='Theorem',
        ref=str(i),chapter='Families',chapter_label='chap:families',section='',role='planned' if i==64 else 'reference',
        status='planned' if i==64 else 'formalised',review='unreviewed',lean=[],aliases=[],topics=['Jacobi'],
        text='A complete mathematical statement',math='',citations=[]) for i in range(65)]
    (out/'search-index.json').write_text(json.dumps(entries))
    (out/'legacy-urls.json').write_text('{}')
    body='''<!doctype html><html><head><meta charset="utf-8"></head><body><header></header>
<main><section id="rv-reference-search"></section>
<details id="outer"><summary>Supporting</summary><div id="target"><details id="formal"><summary>Formalisation</summary>
<details id="related"><summary>Related</summary><div data-lean-name="Polynomial.derivative_gegenbauer">Statement</div></details>
</details></div></details><pre id="test-report">RUNNING</pre></main>'''
    body+=f'<script src="{(ROOT/"blueprint/src/revolver.js").as_uri()}"></script>'
    body+=f'<script src="{(ROOT/"test/revolver_browser.js").as_uri()}"></script></body></html>'
    (out/'index.html').write_text(body)
    return out/'index.html'

if __name__=='__main__':
    fixture=prepare()
    if '--run' not in sys.argv: print(fixture.as_uri());sys.exit(0)
    chrome=os.environ['CHROME_BIN']
    p=subprocess.run([chrome,'--headless','--disable-gpu','--no-first-run','--no-default-browser-check',
        '--allow-file-access-from-files',f'--user-data-dir={ROOT/".tools/revolver-test-profile"}',
        '--dump-dom','--virtual-time-budget=10000',fixture.as_uri()],capture_output=True,text=True,timeout=90)
    (ROOT/'.tools/revolver-browser-tests.log').write_text(p.stdout+'\n'+p.stderr)
    if p.returncode or 'data-result="pass"' not in p.stdout:
        raise SystemExit('Browser tests failed; see .tools/revolver-browser-tests.log')
    import re
    print(re.search(r'PASS \d+ browser assertions',p.stdout)[0])
