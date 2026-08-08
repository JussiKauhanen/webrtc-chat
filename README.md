# NearChat Direct

NearChat Direct lets two nearby devices send text and images to each other.

It has no accounts. It does not use a chat server, STUN, or TURN.

## How it works

```mermaid
flowchart TD
    A[Open the page on both devices] --> B[Press Connect]
    B --> C[Cameras find the small QR code]
    C --> D[Three beeps choose which device shares first]
    D --> E[The devices scan the offer and answer QR codes]
    E --> F[WebRTC opens a direct link]
    F --> G[Send text and images]
    G --> H[Pings check that the link is still live]
```

## Images

- Select up to 20 images at once.
- Images are made no larger than 1600 by 1600 pixels.
- WebP is used first. JPEG is the backup.
- Each sent image is kept under 2 MB.
- Location and camera details are removed.
- Images are sent one at a time in the order selected.

## Files

- `index.html` holds the page.
- `styles.css` holds the page style.
- `app.js` holds the chat and pairing code.
- `assets/` holds the QR and RaptorQ files.

## Hosting

The app can run on GitHub Pages. Camera and microphone access need HTTPS or localhost.
