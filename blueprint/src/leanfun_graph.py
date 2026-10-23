"""Adjust leanblueprint's graph: Mathlib colour, proof attachment and the reader's legend."""


def ProcessOptions(options, document):
    graph = document.userdata["dep_graph"]
    graph["colors"]["mathlib"] = ("#7040A0", "Purple")
    default_fill = graph["fillcolorizer"]

    def fillcolorizer(node):
        fill = default_fill(node)
        # Preserve whether the proof/definition is marked complete.
        if node.userdata.get("mathlibok") and fill:
            return "#EEE4F7"
        return fill

    graph["fillcolorizer"] = fillcolorizer
    # A reader's key. It replaces the default developer legend, which leanblueprint
    # extends at post-parse order 150 and leanfunreview's icons would otherwise follow.
    def make_legend():
        graph["legend"][:] = [
            ("Box", "definition"),
            ("Ellipse", "theorem or lemma"),
            ("Green", "proved in Lean (dark green: everything it uses is proved too)"),
            ("Purple", "taken from Mathlib"),
            ("Blue or orange outline", "planned, not yet in Lean"),
            ("\U0001F642", "statement checked by a human reviewer"),
            ("\U0001F916", "statement not yet checked by a human"),
            ("\U0001FAE5", "changed since its human check"),
            ("Click", "show the statement, double-click to zoom"),
        ]

    document.addPostParseCallbacks(170, make_legend)

    # plastexdepgraph (order 100) finds a proof's statement by walking back through the
    # siblings of the proof's paragraph, so a statement opening a `supporting` block is
    # missed. Attach each proof to the nearest preceding statement in document order;
    # an explicit \proves (order 10) still wins.
    def attach_proofs():
        last = None

        def walk(node):
            nonlocal last
            for child in node.childNodes or []:
                if child.nodeName == "thmenv":
                    last = child
                elif child.nodeName == "proof" and last is not None:
                    child.userdata.setdefault("proves", last)
                walk(child)

        walk(document)

    document.addPostParseCallbacks(90, attach_proofs)
