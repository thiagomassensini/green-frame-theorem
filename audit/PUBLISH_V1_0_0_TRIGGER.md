# Publish v1.0.0 trigger

This branch-only marker triggers the minimal audited publication workflow. The workflow checks out `main`, reruns the complete Lean and trust gate, creates the annotated `v1.0.0` tag, and publishes the checksummed GitHub Release bundle.
