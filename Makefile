# Common dev commands for the formulation-bench package.
# Run from the repository root.

.PHONY: help install test cov cov-open cov-clean lint format typecheck check docs docs-serve docs-clean clean

help:
	@echo "Targets:"
	@echo "  install      Sync deps with uv"
	@echo "  test         Run pytest"
	@echo "  cov          Run pytest with coverage; writes HTML to htmlcov/ and XML to coverage.xml"
	@echo "  cov-open     Open the HTML coverage report"
	@echo "  cov-clean    Remove coverage artifacts"
	@echo "  lint         Run ruff check"
	@echo "  format       Run ruff format + ruff check --fix"
	@echo "  typecheck    Run mypy"
	@echo "  check        Run lint + typecheck + test"
	@echo "  docs         Build the Sphinx docs once"
	@echo "  docs-serve   Live-reload docs in browser"
	@echo "  docs-clean   Remove built docs"
	@echo "  clean        Remove build + cache artifacts"

install:
	uv sync

test:
	uv run pytest

cov:
	uv run pytest \
		--cov=formulation_bench \
		--cov-report=term-missing \
		--cov-report=html \
		--cov-report=xml

cov-open: cov
	@python -c "import os, webbrowser; webbrowser.open('file://' + os.path.abspath('htmlcov/index.html'))"

cov-clean:
	rm -rf htmlcov coverage.xml .coverage

lint:
	uv run ruff check src tests scripts

format:
	uv run ruff format src tests scripts
	uv run ruff check --fix src tests scripts

typecheck:
	uv run mypy

check: lint typecheck test

docs:
	uv run --extra docs sphinx-build -W -b html docs docs/_build/html

docs-serve:
	uv run --extra docs bash docs/serve.sh

docs-clean:
	rm -rf docs/_build

clean: docs-clean cov-clean
	rm -rf _build build dist .pytest_cache .mypy_cache .ruff_cache
	find . -type d -name __pycache__ -exec rm -rf {} +
