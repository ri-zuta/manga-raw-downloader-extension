// Klik ikon ekstensi: tampilkan/sembunyikan panel di tab aktif.
// content.js (world MAIN) menyediakan window.__mduiToggle().
chrome.action.onClicked.addListener(async (tab) => {
  if (!tab || tab.id == null) return;
  const target = { tabId: tab.id };

  try {
    const [res] = await chrome.scripting.executeScript({
      target,
      world: 'MAIN',
      func: () => {
        if (typeof window.__mduiToggle === 'function') {
          window.__mduiToggle();
          return true;
        }
        return false;
      }
    });
    if (res && res.result) return;

    // Content script belum terpasang di tab ini (mis. tab dibuka sebelum ekstensi di-reload):
    // pasang sekarang lalu buka panelnya. Hook CORS akan "terlambat" sampai halaman di-reload.
    await chrome.scripting.executeScript({ target, world: 'MAIN', files: ['content.js'] });
    await chrome.scripting.executeScript({
      target,
      world: 'MAIN',
      func: () => { if (typeof window.__mduiToggle === 'function') window.__mduiToggle(); }
    });
  } catch (e) {
    // Halaman terlarang (chrome://, Web Store, dll.) tidak bisa disisipi script
    console.warn('Manga Downloader: panel tidak bisa dibuka di tab ini.', e);
  }
});
