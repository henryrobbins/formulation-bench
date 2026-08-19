import sys
from importlib.metadata import version as _pkg_version
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / "_ext"))

_MONO_STACK = "'Roboto Mono', ui-monospace, SFMono-Regular, Menlo, monospace"

project = "formulation_bench"
author = "Henry Robbins"
copyright = "2026, Henry Robbins"
release = _pkg_version("formulation-bench")

extensions = [
    "myst_parser",
    "sphinx.ext.autodoc",
    "sphinx.ext.extlinks",
    "sphinx.ext.viewcode",
    "sphinx.ext.intersphinx",
    "numpydoc",
    "sphinx_design",
    "sphinxcontrib.bibtex",
    "gen_problem_pages",
]

# The bibliography ships with the dataset so the published tarball carries
# full attribution for every problem and formulation source.
bibtex_bibfiles = ["../dataset/ref.bib"]
bibtex_default_style = "plain"

extlinks = {
    "github": (
        "https://github.com/henryrobbins/formulation-bench%s",
        "GitHub%.0s",
    ),
    "paper": ("https://flare.henryrobbins.com%s", "FLARE Paper%.0s"),
    "mf": (
        "https://milp-flare.henryrobbins.com/en/latest%s",
        "milp-flare%.0s",
    ),
}

myst_enable_extensions = [
    "attrs_inline",
    "colon_fence",
    "deflist",
    "fieldlist",
    "dollarmath",
    "amsmath",
    "substitution",
]

myst_substitutions = {
    "GitHub": "[GitHub](https://github.com/henryrobbins/formulation-bench)",
    "FLARE Paper": "[FLARE Paper](https://flare.henryrobbins.com)",
    "milp-flare": "[milp-flare](https://milp-flare.henryrobbins.com/en/latest)",
}

intersphinx_mapping = {
    "python": ("https://docs.python.org/3", None),
}

templates_path = ["_templates"]
exclude_patterns = ["_build", "Thumbs.db", ".DS_Store", "**/*.ai"]

html_theme = "furo"
html_title = "FormulationBench"
html_static_path = ["_static", "brand"]
html_css_files = ["custom.css"]
html_favicon = "brand/logo.svg"

html_theme_options = {
    # The wordmarks carry the project name, so the text version is redundant.
    "light_logo": "wordmark_light.svg",
    "dark_logo": "wordmark_dark.svg",
    "sidebar_hide_name": True,
    "navigation_with_keys": True,
    "source_repository": "https://github.com/henryrobbins/formulation-bench/",
    "source_branch": "main",
    "source_directory": "docs/",
    "footer_icons": [
        {
            "name": "GitHub",
            "url": "https://github.com/henryrobbins/formulation-bench",
            # Furo ships no icon font, so the mark is inlined as SVG.
            "html": """
                <svg stroke="currentColor" fill="currentColor" stroke-width="0"
                     viewBox="0 0 16 16">
                  <path fill-rule="evenodd" d="M 8 0 C 3.58 0 0 3.58 0 8 c 0
                      3.54 2.29 6.53 5.47 7.59 .4 .07 .55 -.17 .55 -.38 0
                      -.19 -.01 -.82 -.01 -1.49 -2.01 .37 -2.53 -.49 -2.69
                      -.94 -.09 -.23 -.48 -.94 -.82 -1.13 -.28 -.15 -.68 -.52
                      -.01 -.53 .63 -.01 1.08 .58 1.23 .82 .72 1.21 1.87 .87
                      2.33 .66 .07 -.52 .28 -.87 .51 -1.07 -1.78 -.2 -3.64
                      -.89 -3.64 -3.95 0 -.87 .31 -1.59 .82 -2.15 -.08 -.2
                      -.36 -1.02 .08 -2.12 0 0 .67 -.21 2.2 .82 .64 -.18 1.32
                      -.27 2 -.27 s 1.36 .09 2 .27 c 1.53 -1.04 2.2 -.82 2.2
                      -.82 .44 1.1 .16 1.92 .08 2.12 .51 .56 .82 1.27 .82
                      2.15 0 3.07 -1.87 3.75 -3.65 3.95 .29 .25 .54 .73 .54
                      1.48 0 1.07 -.01 1.93 -.01 2.2 0 .21 .15 .46 .55 .38 A
                      8.012 8.012 0 0 0 16 8 c 0 -4.42 -3.58 -8 -8 -8 z"></path>
                </svg>
            """,
            "class": "",
        },
    ],
    "light_css_variables": {
        "color-brand-primary": "#b41f2b",
        "color-brand-content": "#a01c26",
        "color-brand-visited": "#a01c26",
        "color-background-primary": "#ffffff",
        "color-background-secondary": "#f7f5f4",
        "color-background-border": "#e8e2df",
        "color-foreground-primary": "#14120f",
        "color-foreground-secondary": "#4f4944",
        "color-foreground-muted": "#867d76",
        "color-foreground-border": "#ded7d4",
        "color-sidebar-background": "#f7f5f4",
        "color-sidebar-background-border": "#e8e2df",
        "color-sidebar-brand-text": "#14120f",
        "color-sidebar-link-text": "#4f4944",
        "color-sidebar-link-text--top-level": "#4f4944",
        "color-sidebar-item-background--current": "#fbeceb",
        "color-sidebar-item-background--hover": "#f0ebe8",
        "color-sidebar-search-border": "#ded7d4",
        "color-toc-item-text": "#615a54",
        "color-toc-item-text--active": "#a01c26",
        "color-inline-code-background": "#f2eeec",
        "color-code-background": "#fbfaf9",
        "color-code-foreground": "#33302c",
        "color-api-background": "#fdf7f6",
        "color-api-background-hover": "#fbeceb",
        "color-api-name": "#b41f2b",
        "color-api-pre-name": "#c1665f",
        "color-api-keyword": "#9a3412",
        "color-api-paren": "#6b7684",
        "color-highlight-on-target": "#fdeeec",
        # custom variables consumed by custom.css
        "color-api-signature-accent": "#f0c4b6",
        "color-api-section-border": "#f4dedb",
        "color-content-foreground": "#26231f",
        "font-stack": "'Public Sans', system-ui, -apple-system, sans-serif",
        "font-stack--monospace": _MONO_STACK,
    },
    "dark_css_variables": {
        "color-brand-primary": "#f0938a",
        "color-brand-content": "#ef9d90",
        "color-brand-visited": "#ef9d90",
        "color-background-primary": "#171513",
        "color-background-secondary": "#201d1b",
        "color-background-border": "#332e2b",
        "color-foreground-primary": "#efebe8",
        "color-foreground-secondary": "#b5aca6",
        "color-foreground-muted": "#8d847d",
        "color-foreground-border": "#3d3733",
        "color-sidebar-background": "#201d1b",
        "color-sidebar-background-border": "#332e2b",
        "color-sidebar-brand-text": "#efebe8",
        "color-sidebar-link-text": "#c9c0ba",
        "color-sidebar-link-text--top-level": "#c9c0ba",
        "color-sidebar-item-background--current": "#3a2320",
        "color-sidebar-item-background--hover": "#282422",
        "color-sidebar-search-border": "#3d3733",
        "color-toc-item-text": "#a79e97",
        "color-toc-item-text--active": "#f0938a",
        "color-inline-code-background": "#282422",
        "color-code-background": "#1c1a18",
        "color-code-foreground": "#e0dbd6",
        "color-api-background": "#232019",
        "color-api-background-hover": "#3a2320",
        "color-api-name": "#f0938a",
        "color-api-pre-name": "#c1776c",
        "color-api-keyword": "#e0a07a",
        "color-api-paren": "#9a918a",
        "color-highlight-on-target": "#3a2320",
        "color-api-signature-accent": "#b41f2b",
        "color-api-section-border": "#4a2b26",
        "color-content-foreground": "#e6e0db",
        "font-stack": "'Public Sans', system-ui, -apple-system, sans-serif",
        "font-stack--monospace": _MONO_STACK,
    },
}

# Match Pygments to the palette (Furo supports separate light/dark styles)
pygments_style = "friendly"
pygments_dark_style = "one-dark"

autodoc_default_options = {"members": True, "undoc-members": True}
autodoc_typehints = "none"
numpydoc_class_members_toctree = False
numpydoc_show_class_members = False
numpydoc_xref_param_type = True
numpydoc_xref_ignore = {"of", "or", "optional", "default"}
numpydoc_xref_aliases = {
    "Problem": "formulation_bench.problem.Problem",
    "Formulation": "formulation_bench.formulation.Formulation",
    "Parameter": "formulation_bench.models.Parameter",
    "ParameterType": "formulation_bench.models.ParameterType",
    "Variable": "formulation_bench.models.Variable",
    "VariableType": "formulation_bench.models.VariableType",
    "Shape": "formulation_bench.models.Shape",
    "Dimension": "formulation_bench.models.Dimension",
    "DimensionType": "formulation_bench.models.DimensionType",
    "Definition": "formulation_bench.models.Definition",
    "Assumption": "formulation_bench.models.Assumption",
    "Constraint": "formulation_bench.models.Constraint",
    "Objective": "formulation_bench.models.Objective",
    "Solution": "formulation_bench.models.Solution",
    "Expression": "formulation_bench.models.Expression",
    "ParameterMap": "formulation_bench.models.ParameterMap",
    "Reformulation": "formulation_bench.reformulation.Reformulation",
    "download_dataset": "formulation_bench.download_dataset",
}
