# Byte-preserved paper source

The original `TEOREMA_FRAME_GREEN_TODAS_AS_BASES.md` is stored as three ordered, gzip-compressed Base64 chunks because the publication agent transports repository text objects individually.

Reconstruct and verify it with:

```bash
python3 scripts/materialize_source.py
```

Expected result:

```text
path: docs/90_PAPER_SPECIFICATION.md
bytes: 50630
sha256: 366dfa007002c1d3dbf2eb7c283c13c1b35233647163753ee39e45dd0645c3f4
```

The release workflow materializes the readable Markdown before building the source archive.
