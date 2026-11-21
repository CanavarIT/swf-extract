# swf_extract

Extract every asset from SWF (Adobe Flash) files using **only the Python standard library**.

`swf_extract` is a single-file command-line tool. It parses SWF files (uncompressed, zlib and LZMA), pulls out the embedded assets, renders vector graphics to SVG, rebuilds fonts, and decompiles ActionScript 1/2/3 back into readable source.

## Features

- **Single file, zero required dependencies.** All internal modules are embedded in `swf_extract.py`; only Python 3 is needed.
- **Compression support:** uncompressed (`FWS`), zlib (`CWS`) and LZMA (`ZWS`) SWF files.
- **Images:** JPEG, PNG and GIF bitmaps, including lossless bitmaps (decoded to PNG) and JPEG with alpha channel (merged to PNG when Pillow is available).
- **Sounds:** event sounds and streaming audio (WAV / MP3 where possible; Nellymoser and Speex are dumped as raw `.bin` streams).
- **Vector shapes and morph shapes:** exported as SVG.
- **Sprites (MovieClips):** rendered as animated SVG, with an optional per-frame static SVG export.
- **Buttons:** every state (`up`, `over`, `down`, `hit`) exported as a separate SVG.
- **Fonts:** rebuilt as `.ttf` / `.otf` / `.cff` files.
- **Texts:** static and dynamic text.
- **Video:** embedded video streams exported as FLV.
- **Binary data:** `DefineBinaryData` payloads, with nested SWF files extracted recursively (up to 3 levels deep).
- **Scripts:**
  - ActionScript 1/2 decompiled to `.as`, with a disassembly in `.asm.txt` (frame scripts, `DoInitAction`, clip actions and button actions).
  - ActionScript 3 (ABC) decompiled and disassembled.
  - Code that can't be structured is kept as `// goto` comments, so nothing is lost.
- **Timelines:** display lists, frame labels and sounds dumped as JSON.
- **Metadata:** `info.json` (stage size, FPS, frame count, tag histogram, symbols, exports, scenes, etc.) and `manifest.json` (every extracted file).

## Requirements

- Python 3.8 or newer
- *(Optional)* [Pillow](https://pypi.org/project/Pillow/) — used to merge JPEG + alpha channel into a single PNG. Without it, the alpha channel is saved next to the JPEG as `*.alpha.bin`.

## Installation

No installation needed. Download `swf_extract.py` and run it:

```bash
git clone https://github.com/CanavarIT/swf-extract.git
cd swf-extract
python swf_extract.py --help
```

## Usage

```bash
# Extract everything from one file into ./out/game/
python swf_extract.py game.swf -o out

# Extract only some categories from several files, plus per-frame SVGs
python swf_extract.py *.swf --only sprites,scripts,fonts --frames

# Just show what's inside the file (no extraction)
python swf_extract.py game.swf --list

# Process a whole folder (searched recursively for *.swf)
python swf_extract.py ./flash_games -o extracted

# Skip ActionScript decompilation
python swf_extract.py game.swf --no-decompile
```

Inputs can be files, glob patterns or directories. Each SWF is extracted into its own subfolder: `<out>/<swf name>/`.

## Options

| Option | Description |
| --- | --- |
| `inputs` | One or more SWF files, glob patterns or folders. |
| `-o`, `--out` | Output directory (default: `swf_out`). |
| `--only` | Comma-separated list of categories to extract (see below). Default: all. |
| `--skip` | Comma-separated list of categories to skip. |
| `--frames` | Also export every frame of every sprite as a separate static SVG. |
| `--max-frames N` | Maximum number of frames per animation (`0` = unlimited). |
| `--raw` | Additionally dump raw tags. |
| `--no-decompile` | Don't decompile ActionScript. |
| `--list` | Only print the file summary (version, stage size, FPS, frame count, tag histogram). |

### Categories

`images`, `sounds`, `shapes`, `morphs`, `sprites`, `fonts`, `texts`, `video`, `binary`, `scripts`, `buttons`, `timelines`

## Output layout

```
out/
└── game/
    ├── images/      # png / jpg / gif
    ├── sounds/      # wav / mp3 / raw streams
    ├── shapes/      # svg
    ├── morphs/      # svg
    ├── sprites/     # svg (main.svg is the main timeline)
    ├── buttons/     # svg, one per button state
    ├── fonts/       # ttf / otf / cff
    ├── texts/
    ├── video/       # flv
    ├── binary/      # DefineBinaryData payloads (nested SWFs are extracted too)
    ├── scripts/     # .as and .asm.txt
    ├── timelines/   # json
    ├── info.json
    └── manifest.json
```

## Notes and limitations

- Decompiled ActionScript is a best-effort reconstruction and may not recompile as-is.
- Some legacy audio codecs (Nellymoser, Speex) are saved as raw streams rather than converted.
- Rendering is SVG-based; some advanced Flash features (certain filters, blend modes or masks) may not look identical to the Flash Player.
- Malformed or truncated tags are skipped with a warning on `stderr`; extraction continues with the rest of the file.

## License

This project is licensed under the [MIT License](LICENSE).
