"""Hash-bound human review display; HTML only, independent of proof completion."""
import json
from pathlib import Path
import subprocess
import sys

from jinja2 import Template
from plasTeX.PackageResource import PackageCss, PackagePreCleanupCB


def review_status(names, statuses):
    if any(statuses.get(n) == 'stale' for n in names):
        return 'stale'
    if names and all(statuses.get(n) == 'reviewed-current' for n in names):
        return 'reviewed-current'
    return 'unreviewed'


def review_style(original, status, filled):
    styles = [s.strip() for s in original.split(',') if s.strip()]
    if filled and 'filled' not in styles:
        styles.append('filled')
    if status == 'reviewed-current':
        styles.append('bold')
    elif status == 'stale':
        styles.append('dashed')
    return ','.join(dict.fromkeys(styles))


HUMAN = '\U0001F642'
ROBOT = '\U0001F916'
STALE = '\U0001FAE5'


def ProcessOptions(options, document):
    if document.config['general']['renderer'] != 'HTML5':
        return
    root = Path(__file__).resolve().parents[2]
    status_file = root / 'review/status.json'
    subprocess.run([sys.executable, str(root / 'scripts/review.py'),
                    'status', '--json', str(status_file)], cwd=root, check=True)
    data = json.loads(status_file.read_text())
    statuses = data['declarations']
    node_statuses = data.get('nodes', {})

    def status_for(node):
        return node_statuses.get(getattr(node, 'id', None),
            review_status(node.userdata.get('leandecls', []), statuses))
    graph = document.userdata['dep_graph']
    original = graph.get('stylerizer', lambda node: '')

    def style(node):
        status = status_for(node)
        return review_style(original(node), status, bool(graph['fillcolorizer'](node)))

    graph['stylerizer'] = style

    def icon_for(node, status):
        # Mathlib results and planned nodes without Lean declarations get no icon.
        if node.userdata.get('mathlibok') or not node.userdata.get('leandecls'):
            return ''
        return {'reviewed-current': HUMAN, 'stale': STALE}.get(status, ROBOT)

    def annotate():
        for g in graph['graphs'].values():
            for node in g.nodes:
                status = status_for(node)
                node.userdata['statement_review'] = status
                node.userdata['review_icon'] = icon_for(node, status)
    document.addPostParseCallbacks(160, annotate)

    # Review banner for the README: human-reviewed, stale and LLM-only statements.
    def write_banner(renderer):
        nodes = {id(n): n for g in graph['graphs'].values() for n in g.nodes}.values()
        human, stale, llm = banner_counts(nodes)
        Path('review-status.svg').write_text(review_banner(human, stale, llm))
        Path('review-counts.json').write_text(json.dumps(
            {'human_reviewed': human, 'stale': stale, 'llm_only': llm}) + '\n')
        return []
    document.addPackageResource(PackagePreCleanupCB(data=write_banner))

    # The dependency graph hard-codes node labels; append the review icon.
    from plastexdepgraph.Packages import depgraph
    if not getattr(depgraph.DepGraph.to_dot, '_review_icons', False):
        original_to_dot = depgraph.DepGraph.to_dot

        def to_dot(self, shapes):
            dot = original_to_dot(self, shapes)
            for node in self.nodes:
                icon = node.userdata.get('review_icon')
                if icon:
                    n = dot.get_node(node.id)
                    n.attr['label'] = f"{n.attr['label']} {icon}"
            return dot
        to_dot._review_icons = True
        depgraph.DepGraph.to_dot = to_dot
    document.userdata.setdefault('thm_header_extras_tpl', []).append(Template('''
      {% if obj.userdata.review_icon %}
      {% if obj.userdata.statement_review == 'reviewed-current' %}
      <span class="statement-review" title="All linked Lean statements have current human reviews; proofs are not reviewed">
        {{ obj.userdata.review_icon }} human-reviewed
      </span>
      {% elif obj.userdata.statement_review == 'stale' %}
      <span class="statement-review stale" title="A linked Lean statement or the book text changed after its human review">
        {{ obj.userdata.review_icon }} human review stale
      </span>
      {% else %}
      <span class="statement-review" title="Formalised and checked by Lean; the statement is not yet human-reviewed">{{ obj.userdata.review_icon }}</span>
      {% endif %}
      {% endif %}
    '''))
    document.addPackageResource(PackageCss(path=Path(__file__).parent / 'review.css'))

    def copy_badge(renderer):
        import shutil
        shutil.copyfile(root / 'review/statement-reviewed.svg', 'statement-reviewed.svg')
        return ['statement-reviewed.svg']
    document.addPackageResource(PackagePreCleanupCB(data=copy_badge))


def banner_counts(nodes):
    """(human-reviewed, stale, LLM-only) counts over nodes carrying a review icon."""
    statuses = [n.userdata.get('statement_review') for n in nodes if n.userdata.get('review_icon')]
    human = statuses.count('reviewed-current')
    stale = statuses.count('stale')
    return human, stale, len(statuses) - human - stale


def review_banner(human, stale, llm):
    """An SVG bar: human-reviewed on the left, stale reviews next, LLM-only on the right."""
    total = max(human + stale + llm, 1)
    width, left, bar_w, y = 640, 20, 600, 34
    hw = round(bar_w * human / total)
    sw = round(bar_w * stale / total)
    hp, sp, lp = (100 * k / total for k in (human, stale, llm))
    font = 'font-family="-apple-system,Segoe UI,Helvetica,Arial,sans-serif"'
    return f'''<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="92" viewBox="0 0 {width} 92">
  <title>LeanFun statements: {human} human-reviewed, {stale} with a stale human review, {llm} LLM-only (not yet human-reviewed)</title>
  <rect x="0" y="0" width="{width}" height="92" rx="10" fill="#f6f8fa"/>
  <text x="{width // 2}" y="22" text-anchor="middle" {font} font-size="14" font-weight="600" fill="#24292e">Statement review in the LeanFun RevOLVER</text>
  <clipPath id="bar"><rect x="{left}" y="{y}" width="{bar_w}" height="20" rx="10"/></clipPath>
  <g clip-path="url(#bar)">
    <rect x="{left}" y="{y}" width="{bar_w}" height="20" fill="#f07c12"/>
    <rect x="{left + hw}" y="{y}" width="{sw}" height="20" fill="#cf222e"/>
    <rect x="{left}" y="{y}" width="{hw}" height="20" fill="#0a6fd8"/>
  </g>
  <text x="{left}" y="78" {font} font-size="14" fill="#0a6fd8">\U0001F642 human-reviewed: {human} ({hp:.0f}%)</text>
  <text x="{width // 2}" y="78" text-anchor="middle" {font} font-size="14" fill="#cf222e">\U0001FAE5 review stale: {stale} ({sp:.0f}%)</text>
  <text x="{left + bar_w}" y="78" text-anchor="end" {font} font-size="14" fill="#c4600a">LLM-only: {llm} ({lp:.0f}%) \U0001F916</text>
</svg>
'''
