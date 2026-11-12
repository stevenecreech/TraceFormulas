
const $ = (selector, root = document) => root.querySelector(selector);
const esc = value => String(value ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
let series, currentVolume, outline, published, records = [], nodes = new Map(), currentRecord = null;
let globalMapMode = 'outline', mapTarget = '';
const sidebarExpanded = new Map();
const tabDefs = [
  ['read','Read','book'], ['watch','Watch','play'], ['formal','Formalization','code'],
  ['compare','Compare','columns'], ['map','Map','map']
];
const paths = {
  book:'M4 4h6a3 3 0 0 1 3 3v14a4 4 0 0 0-4-3H4z M20 4h-4a3 3 0 0 0-3 3v14a4 4 0 0 1 4-3h3z',
  grid:'M4 4h6v6H4z M14 4h6v6h-6z M4 14h6v6H4z M14 14h6v6h-6z',
  map:'M12 3v6 M5 16v-4h14v4 M9 3h6v4H9z M2 16h6v5H2z M16 16h6v5h-6z',
  compass:'M21 12a9 9 0 1 1-18 0 9 9 0 0 1 18 0 M15 9l-2 4-4 2 2-4z',
  search:'M20 20l-5-5 M17 10a7 7 0 1 1-14 0 7 7 0 0 1 14 0',
  arrow:'M4 12h15 M13 6l6 6-6 6', chevron:'M9 5l7 7-7 7',
  play:'M9 6l10 6-10 6z M3 4v16',
  code:'M8 6l-6 6 6 6 M16 6l6 6-6 6 M14 3l-4 18',
  columns:'M3 4h18v16H3z M12 4v16',
  pen:'M4 20l4-1L20 7l-4-4L4 15z M13 6l4 4',
  menu:'M3 5h18 M3 12h18 M3 19h18',
  close:'M6 6l12 12 M18 6L6 18',
  info:'M12 11v6 M12 7h.01 M21 12a9 9 0 1 1-18 0 9 9 0 0 1 18 0',
  external:'M14 3h7v7 M21 3L10 14 M10 4H4v16h16v-6',
  download:'M12 3v12 M7 10l5 5 5-5 M4 17v4h16v-4',
  check:'M5 12l4 4L20 5'
};
function icon(name, size = 16) {
  return '<svg width="'+size+'" height="'+size+'" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="'+(paths[name]||paths.book)+'"/></svg>';
}
function safeURL(value) {
  try { const u = new URL(value); return ['https:','http:'].includes(u.protocol) ? u.href : ''; } catch { return ''; }
}
function contentURL(value) {
  if (typeof value !== 'string' || !value.trim()) return '';
  try { const u = new URL(value, document.baseURI); return ['https:','http:'].includes(u.protocol) ? u.href : ''; } catch { return ''; }
}
function renderedHTML(value) {
  if (!value) return '';
  const template = document.createElement('template');
  template.innerHTML = value;
  const allowed = new Set(['P','DIV','SPAN','H1','H2','H3','H4','H5','H6','A','UL','OL','LI','DL','DT','DD','BLOCKQUOTE','PRE','CODE','STRONG','EM','DEL','HR','BR','TABLE','CAPTION','THEAD','TBODY','TR','TH','TD','FIGURE','FIGCAPTION','IMG','SUP','SUB']);
  const forbidden = new Set(['SCRIPT','STYLE','IFRAME','OBJECT','EMBED','FORM','INPUT','BUTTON','TEXTAREA','SELECT','SVG','MATH','LINK','META','BASE']);
  for (const el of Array.from(template.content.querySelectorAll('*'))) {
    if (forbidden.has(el.tagName)) { el.remove(); continue; }
    if (!allowed.has(el.tagName)) { el.replaceWith(...el.childNodes); continue; }
    const href = el.getAttribute('href'), src = el.getAttribute('src'), alt = el.getAttribute('alt');
    const imageWidth = el.tagName === 'IMG' ? el.style.width : '';
    const id = el.id, classes = el.className;
    for (const attr of Array.from(el.attributes)) el.removeAttribute(attr.name);
    if (id) el.id = id;
    if (classes) el.className = classes;
    if (el.tagName === 'A' && href) {
      const valid = href.startsWith('#') ? href : contentURL(href);
      if (valid) { el.setAttribute('href',valid); if (!valid.startsWith('#') && new URL(valid,document.baseURI).origin !== location.origin) { el.target='_blank'; el.rel='noopener noreferrer'; } }
    }
    if (el.tagName === 'IMG') {
      if (contentURL(src)) { el.src=contentURL(src); el.alt=alt||''; el.loading='lazy'; } else el.remove();
      // Preserve only bounded percentage widths, never arbitrary source styles.
      if (/^\d+(?:\.\d+)?%$/.test(imageWidth) && parseFloat(imageWidth) > 0 && parseFloat(imageWidth) <= 100) {
        el.style.width = imageWidth;
      }
    }
  }
  return template.innerHTML;
}
function prose(value) { return '<div class="prose">'+renderedHTML(value)+'</div>'; }
const formalStatusLabels = {
  'not-started': 'Not started',
  'in-progress': 'In progress',
  linked: 'Source linked',
  'autoformalized-awaiting-review': 'Autoformalized · awaiting human review'
};
function formalStatusLabel(status) { return formalStatusLabels[status] || status; }
function volumeLabel() { return 'Volume '+currentVolume.label; }
function volumeURL(volume) { return '?volume='+encodeURIComponent(volume.id)+'#/overview'; }
function sourceLink(path,label) { return path ? '<a class="text-link source-link" href="'+esc(path)+'" download>'+esc(label)+' '+icon('download',13)+'</a>' : ''; }
function seriesView() {
  const numbers=[...new Set(series.volumes.map(v=>v.number))];
  return '<div class="page">'+pageHeading('The complete series','Trace Formulas','Four settings, each developed through automorphic forms, automorphic representations, and a dictionary connecting the two.')+
    numbers.map(number=>{const volumes=series.volumes.filter(v=>v.number===number);return '<section class="series-volume"><p class="eyebrow">Volume '+number+'</p><h2>'+esc(volumes[0].topic)+'</h2><p>'+esc(volumes[0].description)+'</p><div class="series-parts">'+volumes.map(v=>'<a class="series-part" href="'+volumeURL(v)+'"><span class="part-letter">'+v.label+'</span><h3>'+esc(v.perspective)+'</h3><span class="status-label">'+esc(v.status==='planned'?'Planned':'Draft in progress')+'</span></a>').join('')+'</div></section>';}).join('')+'</div>';
}
function blankContent() {
  return {intro:'',sections:{},videos:[],formal:{status:'not-started',summary:'',url:'',declarations:'',sources:[]},comparisons:[],prerequisites:[],sectionPrerequisites:{},exercises:[],explorations:[],resources:[]};
}
function content(id) {
  const c = published.chapters[id] || {};
  return {...blankContent(),...c,formal:{...blankContent().formal,...c.formal}};
}
function chapterLabel(record) { return record.number !== undefined ? 'Chapter '+record.number : 'Appendix '+record.letter; }
function sectionNumber(record, index) { return (record.number ?? record.letter)+'.'+(index+1); }
function chapterLink(record, tab = 'read', section = '') { return record ? '#/chapter/'+record.id+'/'+tab+(section?'/'+section:'') : '#/contents'; }
function nodeLink(id) { const n=nodes.get(id); return n ? chapterLink(n.record,'read',n.sectionId||'') : '#/map'; }
function hasWriting(record) { const c=content(record.id); return !!(c.intro.trim()||Object.values(c.sections).some(t=>t.trim())); }
function route() { return location.hash.replace(/^#\/?/,'').split('/').map(s=>{try{return decodeURIComponent(s);}catch{return s;}}); }
function typeset() {
  if(window.MathJax?.startup?.promise) return window.MathJax.startup.promise.then(()=>window.MathJax.typesetPromise?.([$('#main')])).catch(()=>{});
  return Promise.resolve();
}
function chapterNavigation(record) {
  const active = currentRecord?.id === record.id;
  const key = 'chapter-' + record.id, sectionList = 'nav-sections-' + record.id;
  const expanded = active || sidebarExpanded.get(key) === true;
  const currentSection = active && route()[2] === 'read' ? route()[3] : '';
  const link = '<a class="chapter-nav-link'+(active?' active':'')+'" href="'+chapterLink(record)+'"'+(active&&!currentSection?' aria-current="page"':'')+'><span class="num">'+esc(record.number ?? record.letter)+'</span><span>'+esc(record.title)+'</span></a>';
  if (!record.sections.length) return '<div class="chapter-nav-row">'+link+'</div>';
  return '<div class="chapter-nav-row">'+link+'<button class="chapter-nav-toggle" data-action="chapter-sections" data-sidebar-key="'+esc(key)+'" aria-label="Toggle sections in '+esc(chapterLabel(record))+'" aria-expanded="'+expanded+'" aria-controls="'+esc(sectionList)+'">'+icon('chevron',12)+'</button></div>'+
    '<ul class="section-nav" id="'+esc(sectionList)+'" aria-label="Sections in '+esc(chapterLabel(record))+'"'+(expanded?'':' hidden')+'>'+record.sections.map((section,index)=>'<li><a class="section-nav-link'+(currentSection===section.id?' active':'')+'" href="'+chapterLink(record,'read',section.id)+'"'+(currentSection===section.id?' aria-current="location"':'')+'><span class="section-nav-number">'+esc(sectionNumber(record,index))+'</span><span>'+esc(section.title)+'</span></a></li>').join('')+'</ul>';
}
function renderSidebar() {
  const r=route(), page=r[0]||'series';
  const scrollTop=$('.sidebar-scroll')?.scrollTop||0;
  document.querySelectorAll('.division-nav[data-sidebar-key]').forEach(el=>sidebarExpanded.set(el.dataset.sidebarKey,el.open));
  const top=[['series','All volumes','book'],['overview','Overview','grid'],['contents','Contents','book'],['paths','Reading paths','compass'],['map','Dependency map','map']];
  $('#sidebar').innerHTML=
    '<a class="brand" href="#/series"><span class="brand-mark">τ</span><span><span class="brand-title">Trace Formulas</span><span class="brand-note">A connected mathematics textbook</span></span></a>'+
    '<div class="volume-label"><div><strong>'+esc(volumeLabel())+'</strong><small>'+esc(currentVolume.perspective)+'</small></div><span class="tiny-dot" title="Prototype"></span></div>'+
    '<div class="volume-picker"><label for="volume-select">Choose a volume</label><select id="volume-select">'+series.volumes.map(v=>'<option value="'+v.id+'"'+(v.id===currentVolume.id?' selected':'')+'>'+v.label+' · '+esc(v.perspective)+' · '+esc(v.topic)+'</option>').join('')+'</select></div><div class="sidebar-scroll"><nav class="nav-top" aria-label="Volume"><div>'+top.map(t=>'<a class="nav-link'+(page===t[0]?' active':'')+'" href="#/'+t[0]+'"'+(page===t[0]?' aria-current="page"':'')+'>'+icon(t[2])+' '+t[1]+'</a>').join('')+'</div></nav><p class="nav-label">The volume</p>'+
    outline.divisions.map(d=>'<details class="division-nav" data-sidebar-key="division-'+esc(d.id)+'"'+((currentRecord?.division===d.id||(sidebarExpanded.get('division-'+d.id)??(!currentRecord&&d.id==='A')))?' open':'')+'><summary><span class="division-letter">'+d.id+'</span>'+esc(d.title)+'<span class="chevron">'+icon('chevron',12)+'</span></summary>'+outline.chapters.filter(c=>c.division===d.id).map(chapterNavigation).join('')+'</details>').join('')+
    '<details class="division-nav" data-sidebar-key="appendices"'+((currentRecord?.letter||sidebarExpanded.get('appendices'))?' open':'')+'><summary><span class="division-letter">+</span>Appendices<span class="chevron">'+icon('chevron',12)+'</span></summary>'+outline.appendices.map(chapterNavigation).join('')+'</details>'+
    '<a class="nav-link" style="margin-top:20px" href="#/about">'+icon('info')+' About this edition</a></div>'+
    '<div class="sidebar-footer"><span class="author-monogram">SC</span><span>Steven Creech<small>Author · '+esc(volumeLabel())+'</small></span></div>';
  $('.sidebar-scroll').scrollTop=scrollTop;
}
function renderTopbar() {
  const labels={series:'All volumes',overview:'Overview',contents:'Contents',paths:'Reading paths',map:'Dependency map',about:'About this edition'};
  $('#topbar').innerHTML='<button class="menu-toggle" data-action="menu" aria-label="Open navigation" aria-expanded="false">'+icon('menu',20)+'</button>'+
    '<div class="breadcrumbs"><a class="desktop-crumb" href="#/series">Trace Formulas</a><span class="desktop-crumb">/</span><a href="#/contents">'+esc(volumeLabel())+'</a><span>/</span><span>'+esc(currentRecord?chapterLabel(currentRecord):(labels[route()[0]||'series']||'Overview'))+'</span></div>'+
    '<div class="top-actions"><button class="top-button" data-action="search" aria-label="Search the volume">'+icon('search')+'<span>Search</span><kbd>/</kbd></button></div>';
  const source=safeURL(published.repositoryUrl||'');
  $('#footer').innerHTML='<span>Trace Formulas · '+esc(volumeLabel())+' <span aria-hidden="true">/</span> Steven Creech</span><div class="footer-links"><a href="#/about">About this edition</a>'+(published.acknowledgments?'<a href="#/about/acknowledgments">Funding acknowledgment</a>':'')+'<a href="#/contents">Full contents</a>'+(source?'<a href="'+esc(source)+'" target="_blank" rel="noopener noreferrer">Source</a>':'')+'</div>';
}
function modularArt() {
  return '<figure class="hero-art" aria-label="Illustration of the standard fundamental region in the upper half-plane"><svg viewBox="0 0 440 360" role="img"><title>The upper half-plane and a fundamental region</title><defs><linearGradient id="wash" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#d8e3d5" stop-opacity="0.1"/><stop offset="1" stop-color="#d8e3d5" stop-opacity=".8"/></linearGradient><clipPath id="half"><rect x="22" y="20" width="396" height="264"/></clipPath></defs><g clip-path="url(#half)" fill="none" stroke="#cdd5c6" stroke-width="1"><circle cx="220" cy="282" r="110"/><circle cx="110" cy="282" r="110"/><circle cx="330" cy="282" r="110"/><circle cx="55" cy="282" r="55"/><circle cx="165" cy="282" r="55"/><circle cx="275" cy="282" r="55"/><circle cx="385" cy="282" r="55"/><circle cx="220" cy="282" r="220"/><path d="M55 22v260 M110 22v260 M165 22v260 M220 22v260 M275 22v260 M330 22v260 M385 22v260" stroke-dasharray="2 7" opacity=".7"/></g><path d="M165 31H275V186.74A110 110 0 0 0 165 186.74Z" fill="url(#wash)"/><path d="M165 31v155.74A110 110 0 0 1 275 186.74V31" fill="none" stroke="#347465" stroke-width="1.8"/><path d="M22 282H418" stroke="#a6b69e"/><path d="M220 292V20" stroke="#b4c3a9" stroke-dasharray="3 5"/><circle cx="220" cy="172" r="3" fill="#b96846"/><circle cx="165" cy="186.74" r="3" fill="#347465"/><circle cx="275" cy="186.74" r="3" fill="#347465"/><text x="205" y="114" fill="#347465" font-family="Georgia,serif" font-size="34" font-style="italic">F</text><text x="230" y="170" fill="#b96846" font-family="Georgia,serif" font-size="16" font-style="italic">i</text><g font-family="Georgia,serif" font-size="13" fill="#8a9d7d"><text x="96" y="307">−1</text><text x="151" y="307">−½</text><text x="216" y="307">0</text><text x="270" y="307">½</text><text x="327" y="307">1</text><text x="367" y="65" font-size="29" font-style="italic">ℍ</text><text x="210" y="25">∞</text></g></svg><figcaption class="art-caption"><span>A fundamental region</span><span>ℍ / PSL₂(ℤ)</span></figcaption></figure>';
}
function overviewView() {
  const first=outline.chapters[0];
  const counts={chapters:outline.chapters.length,sections:outline.chapters.reduce((n,c)=>n+c.sections.length,0),appendices:outline.appendices.length};
  if (!first) return '<div class="page">'+pageHeading(volumeLabel()+' · '+currentVolume.perspective,currentVolume.topic,'This volume is planned. Its chapter outline, manuscript, formalizations, and lectures will be developed here.')+'<a class="btn" href="#/series">Explore the series '+icon('arrow',14)+'</a></div>';
  return '<div class="page home-page"><section class="hero"><div><p class="kicker">'+esc(volumeLabel()+' · '+currentVolume.perspective)+'</p><h1>'+esc(outline.subtitle)+'</h1><p class="hero-description">Read the book, follow the formalization, and compare both arguments section by section. Chapter lectures accompany the same mathematics.</p><div class="hero-actions"><a class="btn btn-primary" href="'+chapterLink(first)+'">Open Chapter '+first.number+' '+icon('arrow')+'</a><a class="btn" href="#/contents">Explore the volume</a>'+(currentVolume.pdfUrl?'<a class="btn" href="'+esc(currentVolume.pdfUrl)+'">Download PDF '+icon('download',14)+'</a>':'')+'</div><p class="hero-note"><span class="tiny-dot"></span>Draft edition · '+esc(volumeLabel())+' in preparation</p></div>'+modularArt()+'</section>'+
    '<div class="volume-facts"><div class="fact"><strong>'+counts.chapters+'</strong><span>chapters</span></div><div class="fact"><strong>'+counts.sections+'</strong><span>sections</span></div><div class="fact"><strong>'+counts.appendices+'</strong><span>appendices</span></div></div>'+
    '<section><div class="section-heading"><div><p class="eyebrow">The shape of the book</p><h2>'+outline.divisions.length+' connected divisions</h2></div><a class="text-link" href="#/contents">Full table of contents '+icon('arrow',14)+'</a></div><div class="contents-list">'+outline.divisions.map(d=>'<a class="part-row" href="#/contents/'+d.id+'"><span class="part-letter">'+d.id+'</span><div><h3>'+esc(d.title)+'</h3><p>'+esc(d.subtitle)+'</p></div><span class="part-range">Ch. '+d.start+'–'+d.end+'</span><span class="arrow">'+icon('arrow',18)+'</span></a>').join('')+'</div></section></div>';
}
function pageHeading(kicker,title,description) {
  return '<header class="page-heading"><p class="eyebrow">'+esc(kicker)+'</p><h1>'+esc(title)+'</h1><p class="lede">'+esc(description)+'</p></header>';
}
function contentsView() {
  return '<div class="page">'+pageHeading(volumeLabel(),'Contents',outline.chapters.length+' chapters and '+outline.appendices.length+' appendices. Open a chapter to follow its sections and connections.')+
    '<nav class="outline-filters" aria-label="Jump to division">'+outline.divisions.map(d=>'<a class="filter-chip" href="#/contents/'+d.id+'">'+d.id+' · '+esc(d.title)+'</a>').join('')+'<a class="filter-chip" href="#/contents/appendices">Appendices</a></nav>'+
    outline.divisions.map(d=>'<section class="outline-section" id="division-'+d.id+'"><div class="outline-section-header"><span class="part-letter">'+d.id+'</span><div><h2>'+esc(d.title)+'</h2><p>'+esc(d.subtitle)+' · Chapters '+d.start+'–'+d.end+'</p></div></div>'+outline.chapters.filter(c=>c.division===d.id).map(c=>'<a class="outline-chapter" href="'+chapterLink(c)+'"><span class="chapter-number">'+c.number+'</span><div><h3>'+esc(c.title)+'</h3><p>'+esc(c.endpoint)+'</p><span class="section-mini"><span>'+c.sections.length+' sections</span><span>'+(hasWriting(c)?'Text available':'Planned')+'</span></span></div><span class="arrow">'+icon('arrow',16)+'</span></a>').join('')+'</section>').join('')+
    '<section class="outline-section" id="division-appendices"><div class="outline-section-header"><span class="part-letter">+</span><div><h2>Appendices</h2><p>Background, reference, and proof supplements</p></div></div>'+outline.appendices.map(a=>'<a class="outline-chapter" href="'+chapterLink(a)+'"><span class="chapter-number">'+a.letter+'</span><div><h3>'+esc(a.title)+'</h3><p>'+esc(a.description)+'</p></div><span class="arrow">'+icon('arrow',16)+'</span></a>').join('')+'</section></div>';
}
function tabCount(tab,c) {
  if(tab==='read') return Object.values(c.sections).filter(v=>v.trim()).length||'';
  return ({watch:c.videos.length,formal:c.formal.declarations.split('\n').filter(Boolean).length,compare:c.comparisons.length,map:c.prerequisites.length+Object.values(c.sectionPrerequisites).reduce((s,v)=>s+v.length,0),exercises:c.exercises.length,explore:c.explorations.length})[tab]||'';
}
function emptyView(title,description,ico,tab,slots=[]) {
  return '<div class="empty-view"><div class="empty-icon">'+icon(ico,24)+'</div><h2>'+title+'</h2><p>'+description+'</p>'+(slots.length?'<div class="slot-labels">'+slots.map(s=>'<span>'+s+'</span>').join('')+'</div>':'')+'</div>';
}
function chapterView(record, requestedTab) {
  const tab=tabDefs.some(t=>t[0]===requestedTab)?requestedTab:'read';
  const c=content(record.id);
  let body='';
  if(tab==='read')body=readView(record,c);
  if(tab==='watch')body=watchView(c);
  if(tab==='formal')body=formalView(c);
  if(tab==='compare')body=compareView(c);
  if(tab==='map')body=chapterMapView(record,c);
  const i=records.indexOf(record),prev=records[i-1],next=records[i+1];
  return '<div class="page chapter-page"><header class="chapter-header"><div class="chapter-topline"><p class="eyebrow">'+(record.division?'Division '+record.division+' · '+esc(outline.divisions.find(d=>d.id===record.division).title):'Reference material')+'</p>'+'</div><h1>'+esc(record.title)+'</h1><p class="chapter-description">'+esc(record.description)+'</p><div class="chapter-meta"><span>'+chapterLabel(record)+'</span>'+(record.sections.length?'<span>'+record.sections.length+' sections</span>':'')+'<span class="status-label"><span class="tiny-dot"></span>'+(hasWriting(record)?'Text available':'Content in preparation')+'</span></div></header>'+
    '<nav class="tabs" aria-label="Chapter perspectives">'+tabDefs.map(t=>'<a class="tab'+(tab===t[0]?' active':'')+'" href="'+chapterLink(record,t[0])+'"'+(tab===t[0]?' aria-current="page"':'')+'>'+icon(t[2],15)+t[1]+(tabCount(t[0],c)?'<span class="tab-count">'+tabCount(t[0],c)+'</span>':'')+'</a>').join('')+'</nav>'+body+
    '<nav class="chapter-pager" aria-label="Adjacent chapters">'+(prev?'<a class="pager-link" href="'+chapterLink(prev)+'">'+icon('chevron',14).replace('M9 5l7 7-7 7','M15 5l-7 7 7 7')+'<span><small>Previous · '+chapterLabel(prev)+'</small>'+esc(prev.title)+'</span></a>':'<span></span>')+(next?'<a class="pager-link" href="'+chapterLink(next)+'"><span><small>Next · '+chapterLabel(next)+'</small>'+esc(next.title)+'</span>'+icon('chevron',14)+'</a>':'<span></span>')+'</nav></div>';
}
function readView(record,c) {
  const aside=record.sections.length?'<aside class="reading-aside"><h3>In this chapter</h3>'+record.sections.map((s,i)=>'<a href="'+chapterLink(record,'read',s.id)+'"><span class="aside-number">'+sectionNumber(record,i)+'</span><span>'+esc(s.title)+'</span></a>').join('')+'<div class="aside-later"><h3>Connections</h3><a href="'+chapterLink(record,'map')+'">'+icon('map',13)+' Chapter & section map</a><a href="'+chapterLink(record,'formal')+'">'+icon('code',13)+' Formalization</a></div></aside>':'';
  return '<div class="reading-layout"><article class="reading-content"><div class="chapter-intro">'+(c.intro?prose(c.intro):'<div class="scope-note"><strong>Planned destination</strong><p>'+esc(record.endpoint||record.description)+'</p>'+(record.prerequisites?'<p><strong>Preparation.</strong> '+esc(record.prerequisites)+'</p>':'')+'</div>')+'</div>'+
    (record.sections.length?record.sections.map((s,i)=>'<section class="section-content" id="'+s.id+'"><div class="section-title-row"><div><span class="section-number">SECTION '+sectionNumber(record,i)+'</span><h2>'+esc(s.title)+'</h2></div><a class="section-link" href="'+chapterLink(record,'read',s.id)+'" aria-label="Link to section '+sectionNumber(record,i)+'">#</a></div>'+(c.sections[s.id]?prose(c.sections[s.id]):'<div class="empty-section"><p>Exposition, definitions, examples, and proofs are in preparation.</p></div>')+'</section>').join(''):(!c.intro?emptyView('This appendix is in preparation.','Background material, formulas, and references will accompany the chapter exposition.','book','writing'):''))+
    (c.resources.length?'<section class="section-content"><h2>Further reading</h2><div class="resource-list">'+c.resources.map(r=>externalLink(r.url,r.title,'resource-link')).join('')+'</div></section>':'')+(published.features?.exercises&&c.exercises.length?'<section class="section-content"><h2>Exercises</h2>'+exercisesView(c)+'</section>':'')+(published.features?.explore&&c.explorations.length?'<section class="section-content"><h2>Further exploration</h2>'+exploreView(c)+'</section>':'')+'</article>'+aside+'</div>';
}
function externalLink(url,label,className='btn') {
  const valid=safeURL(url);
  return valid?'<a class="'+className+'" href="'+esc(valid)+'" target="_blank" rel="noopener noreferrer">'+esc(label||'Open resource')+' '+icon('external',13)+'</a>':'<span class="muted">'+esc(label||'Resource')+' · link in preparation</span>';
}
function videoEmbed(video) {
  const valid=safeURL(video.url);
  if(!valid)return '<div class="media-placeholder"><p>This video is in preparation.</p></div>';
  const u=new URL(valid);let embed='';
  if(['www.youtube.com','youtube.com','m.youtube.com','youtu.be'].includes(u.hostname)) {
    let id=u.hostname==='youtu.be'?u.pathname.slice(1):u.searchParams.get('v')||u.pathname.split('/').filter(Boolean).pop();
    if(/^[A-Za-z0-9_-]{11}$/.test(id||''))embed='https://www.youtube-nocookie.com/embed/'+id;
  }
  if(['vimeo.com','www.vimeo.com','player.vimeo.com'].includes(u.hostname)) {
    const id=u.pathname.split('/').filter(Boolean).pop();if(/^\d+$/.test(id||''))embed='https://player.vimeo.com/video/'+id;
  }
  if(embed)return '<iframe class="video-frame" src="'+embed+'" title="'+esc(video.title||'Chapter video')+'" loading="lazy" allow="fullscreen; picture-in-picture; encrypted-media" allowfullscreen referrerpolicy="strict-origin-when-cross-origin"></iframe>';
  if(/\.(mp4|webm)(\?|$)/i.test(valid))return '<video class="video-frame" controls preload="metadata" src="'+esc(valid)+'" aria-label="'+esc(video.title||'Chapter video')+'"></video>';
  return '<div class="media-placeholder"><p>This video opens on its host.</p>'+externalLink(valid,'Watch video')+'</div>';
}
function watchView(c) {
  if(!c.videos.length)return emptyView('See the ideas take shape.','Visual explanations, proof walkthroughs, and tours of the formalization will accompany the written chapter.','play','watch',['Visual intuition','Proof walkthrough','Formalization tour']);
  return c.videos.map(v=>'<article class="media-card"><header class="media-card-head"><p class="eyebrow">'+esc({concept:'Visual explanation',proof:'Proof walkthrough',formalization:'Formalization tour'}[v.kind]||'Video')+'</p><h2>'+esc(v.title||'Untitled video')+'</h2></header>'+videoEmbed(v)+(v.transcript?'<details class="transcript"><summary>Read the transcript</summary>'+prose(v.transcript)+'</details>':'')+'</article>').join('');
}
function formalView(c) {
  if(c.formal.status==='not-started'&&!c.formal.summary&&!c.formal.url&&!c.formal.declarations&&!c.formal.sources.length)return emptyView('Connect the formal argument.','Lean source, declarations, and a description of the scope of formalization will appear here.','code','lean',['Source links','Declaration names','Scope & assumptions']);
  return '<section class="formal-panel"><p class="eyebrow">'+esc(formalStatusLabel(c.formal.status))+'</p><h2>The formalization</h2>'+(c.formal.summary?prose(c.formal.summary):'<p>The scope and conventions of this formalization are in preparation.</p>')+(c.formal.url?'<div style="margin-top:20px">'+externalLink(c.formal.url,'Open formal source')+'</div>':'')+'<div class="declaration-list">'+c.formal.declarations.split('\n').map(x=>x.trim()).filter(Boolean).map(name=>'<code>'+esc(name)+'</code>').join('')+'</div></section>'+c.formal.sources.map(s=>'<section class="formal-panel" id="'+s.sectionId+'"><p class="eyebrow">'+esc(formalStatusLabel(s.status))+'</p><h2>'+esc(s.title)+'</h2>'+sourceLink(s.source,'Download Lean source')+'<pre class="lean-source"><code>'+esc(s.code)+'</code></pre></section>').join('')+'<p class="reference-note">This page displays author-supplied source links and status. It does not run Lean or certify that a declaration matches the written statement.</p>';
}
function compareView(c) {
  if(!c.comparisons.length)return emptyView('Put the two arguments together.','The written section and its Lean source will appear here as they are developed.','columns','compare',['Written argument','Lean source','Alignment notes']);
  return c.comparisons.map(row=>'<article class="comparison" id="'+row.sectionId+'"><h2>'+esc(row.title)+'</h2><div class="comparison-columns"><section class="comparison-column"><p class="eyebrow">In the book</p>'+sourceLink(row.texSource,'Download LaTeX source')+(row.book?prose(row.book):'<p>The exposition is in preparation.</p>')+'</section><section class="comparison-column"><p class="eyebrow">In the formalization · '+esc(formalStatusLabel(row.status))+'</p>'+sourceLink(row.leanSource,'Download Lean source')+(row.lean?'<pre><code>'+esc(row.lean)+'</code></pre>':'<p>No Lean source has been written for this section.</p>')+'</section></div>'+(row.notes?'<section class="comparison-notes"><p class="eyebrow">Alignment notes</p>'+prose(row.notes)+'</section>':'')+'</article>').join('')+'<p class="reference-note">These are the section’s manuscript and Lean source. Displaying a file does not certify its proofs or agreement with the written statement.</p>';
}
function dependencyNode(id) {
  const n=nodes.get(id);return n?'<a class="dep-node" href="'+nodeLink(id)+'">'+esc(n.label)+'</a>':'';
}
function chapterMapView(record,c) {
  const target=record.sections.some(s=>s.id===mapTarget)?mapTarget:record.id;
  const selected=nodes.get(target),prereqs=target===record.id?c.prerequisites:(c.sectionPrerequisites[target]||[]);
  return '<div class="section-heading"><div><p class="eyebrow">Local dependency map</p><h2>What this builds on</h2></div>'+'</div><div class="map-focus-field"><label for="map-focus">Focus</label><select id="map-focus"><option value="'+record.id+'">Whole '+chapterLabel(record).toLowerCase()+'</option>'+record.sections.map((s,i)=>'<option value="'+s.id+'"'+(target===s.id?' selected':'')+'>'+sectionNumber(record,i)+' · '+esc(s.title)+'</option>').join('')+'</select></div>'+
    '<div class="map-legend"><span><span class="legend-line"></span>Prerequisite → selected item</span><span><span class="legend-dot"></span>Connections supplied by the author</span></div><div class="dependency-map">'+
    (prereqs.length?'<div class="dependency-row">'+prereqs.map(dependencyNode).join('')+'</div><div class="dep-connector" aria-label="These prerequisites lead to the selected item">↓</div>':'<p class="dep-caption">Prerequisite connections are in preparation</p>')+
    '<div class="dependency-row"><span class="dep-node current">'+esc(selected.label)+'</span></div>'+
    (target===record.id&&record.sections.length?'<div class="dep-connector" aria-hidden="true">│</div><p class="dep-caption">Contains these sections · outline relationship</p><div class="dependency-row">'+record.sections.map(s=>dependencyNode(s.id)).join('')+'</div>':'')+'</div>'+
    (Object.keys(c.sectionPrerequisites).some(s=>c.sectionPrerequisites[s].length)?'<section class="section-dependency-list"><h3>Section prerequisites</h3>'+record.sections.filter(s=>c.sectionPrerequisites[s.id]?.length).map(s=>'<div class="section-dependency-item"><h3>'+esc(s.title)+'</h3>'+c.sectionPrerequisites[s.id].map(dependencyNode).join('')+'</div>').join('')+'</section>':'')+
    '<p class="reference-note">The outline shows which sections belong to this chapter. Prerequisite arrows describe reading order; they are distinct from proof dependencies extracted from Lean.</p>';
}
function exercisesView(c) {
  if(!c.exercises.length)return emptyView('Turn understanding into practice.','Add exercises with optional hints and solutions. Readers can reveal each step when they are ready.','pen','exercises',['Problems','Hints','Solutions']);
  return c.exercises.map((e,i)=>'<article class="exercise"><p class="eyebrow">Exercise '+(i+1)+'</p><h2>'+esc(e.title||'Exercise '+(i+1))+'</h2>'+prose(e.question)+(e.hint?'<details><summary>Show hint</summary>'+prose(e.hint)+'</details>':'')+(e.solution?'<details><summary>Show solution</summary>'+prose(e.solution)+'</details>':'')+'</article>').join('');
}
function exploreView(c) {
  if(!c.explorations.length)return emptyView('Make the mathematics interactive.','Connect this chapter to a visualization, a computational notebook, or a small experiment. Each exploration opens in its own space.','compass','explore',['Interactive diagrams','Computational notebooks','Worked experiments']);
  return c.explorations.map(e=>'<article class="quiet-panel"><p class="eyebrow">Interactive exploration</p><h3>'+esc(e.title||'Exploration')+'</h3>'+prose(e.description)+externalLink(e.url,'Open exploration')+'</article>').join('');
}
function pathsView() {
  if(!outline.routes.length)return '<div class="page">'+pageHeading(volumeLabel(),'Reading paths','Reading paths will be added as this volume develops.')+'</div>';
  return '<div class="page">'+pageHeading('Ways through the volume','Choose a reading path.','Start with a destination, then follow the relevant chapters. These routes reflect the volume outline; detailed prerequisite edges can be added separately.')+
    '<p class="path-warning">The routes are reading guides. Check each chapter’s preparation notes for background that a route assumes.</p>'+outline.routes.map((p,i)=>'<section class="path-card"><div class="path-card-head"><div><p class="eyebrow">Route '+String(i+1).padStart(2,'0')+'</p><h2>'+esc(p.title)+'</h2></div><a class="btn btn-small" href="'+chapterLink(outline.chapters.find(c=>c.number===p.chapters[0]))+'">Start route '+icon('arrow',13)+'</a></div><p>'+esc(p.description)+'</p><div class="path-steps">'+p.chapters.map((n,i)=>{const c=outline.chapters.find(c=>c.number===n);return(i?'<span class="path-chevron" aria-hidden="true">→</span>':'')+'<a class="path-step" href="'+chapterLink(c)+'" title="'+esc(c.title)+'">'+n+' · '+esc(c.title)+'</a>';}).join('')+'</div></section>').join('')+'</div>';
}
function globalMapView() {
  if(!records.length)return '<div class="page">'+pageHeading(volumeLabel(),'Dependency map','The chapter and section map will grow with the outline.')+'</div>';
  let body='';
  if(globalMapMode==='outline')body='<div class="outline-map">'+outline.divisions.map(d=>'<section class="map-division"><header class="map-division-header"><span>'+d.id+'</span><h2>'+esc(d.title)+'</h2></header><div class="map-children">'+outline.chapters.filter(c=>c.division===d.id).map(c=>'<a class="map-node" href="'+chapterLink(c,'map')+'">'+c.number+' · '+esc(c.title)+'</a>').join('')+'</div></section>').join('')+'</div>';
  else {
    const edges=[];
    records.forEach(r=>{const c=content(r.id);c.prerequisites.forEach(p=>edges.push([p,r.id]));Object.entries(c.sectionPrerequisites).forEach(([s,ps])=>ps.forEach(p=>edges.push([p,s])));});
    body=edges.length?'<div class="section-dependency-list">'+edges.map(([a,b])=>'<div class="section-dependency-item"><div class="dependency-row" style="justify-content:flex-start">'+dependencyNode(a)+'<span aria-label="is a prerequisite of">→</span>'+dependencyNode(b)+'</div></div>').join('')+'</div>':'<div class="empty-view"><div class="empty-icon">'+icon('map',24)+'</div><h2>The dependency graph starts here.</h2><p>Chapter and section prerequisites will appear here as the exposition develops. The outline structure is available now.</p><a class="btn" href="'+chapterLink(outline.chapters[1],'map')+'">Open Chapter 1’s map '+icon('arrow',14)+'</a></div>';
  }
  return '<div class="page">'+pageHeading('How the ideas connect','The map of the volume','Explore the outline, then follow the prerequisite connections entered for individual chapters and sections.')+'<div class="outline-filters"><button class="filter-chip'+(globalMapMode==='outline'?' active':'')+'" data-action="map-mode" data-mode="outline" aria-pressed="'+(globalMapMode==='outline')+'">Outline structure</button><button class="filter-chip'+(globalMapMode==='dependencies'?' active':'')+'" data-action="map-mode" data-mode="dependencies" aria-pressed="'+(globalMapMode==='dependencies')+'">Prerequisite connections</button></div><div class="map-legend"><span><span class="legend-line"></span>'+(globalMapMode==='outline'?'Division contains chapter · not a proof dependency':'Prerequisite → dependent item')+'</span></div>'+body+'</div>';
}
function aboutView() {
  const acknowledgments=published.acknowledgments?'<section class="about-panel acknowledgments" id="acknowledgments" aria-labelledby="acknowledgments-title"><h2 id="acknowledgments-title">Acknowledgments</h2>'+prose(published.acknowledgments)+'</section>':'';
  return '<div class="page">'+pageHeading('The connected textbook','One argument, several perspectives.','A series on trace formulas by Steven Creech: automorphic forms, automorphic representations, and the dictionaries between them.')+'<div class="about-grid"><section class="about-panel"><h2>The written argument</h2><p>Each section’s LaTeX manuscript supplies both this website and the natural-language PDF edition. Unwritten material is marked as in preparation.</p></section><section class="about-panel"><h2>The formal argument</h2><p>Compare displays the manuscript alongside its companion Lean source. Formalization status remains separate from the existence of a source file or a successful website build.</p></section><section class="about-panel"><h2>Lectures</h2><p>Conceptual explanations and proof walkthroughs accompany the chapters. Unrecorded scripts are labeled explicitly.</p></section><section class="about-panel"><h2>The series</h2><p>Begin with SL₂(ℤ), then congruence subgroups with nebentypus, half-integral weight, and quaternionic forms. Each setting has parts a, b, and c.</p><a href="#/series">Browse all volumes</a></section></div>'+acknowledgments+'</div>';
}
function render() {
  const r=route(), page=r[0]||'series';
  currentRecord=page==='chapter'?records.find(c=>c.id===r[1])||null:null;
  renderSidebar();renderTopbar();
  if(page==='chapter'&&!currentRecord)$('#main').innerHTML='<div class="error-page"><h1>Chapter not found</h1><a class="btn" href="#/contents">Return to the contents</a></div>';
  else $('#main').innerHTML=currentRecord?chapterView(currentRecord,r[2]):({series:seriesView,overview:overviewView,contents:contentsView,paths:pathsView,map:globalMapView,about:aboutView}[page]||overviewView)();
  document.title=(currentRecord?chapterLabel(currentRecord)+' · '+currentRecord.title:'Trace Formulas · '+volumeLabel())+' — Steven Creech';
  const renderedHash=location.hash;
  const scrollToTarget=()=>{
    if(location.hash!==renderedHash)return;
    const target=page==='contents'&&r[1]?document.getElementById('division-'+r[1]):page==='chapter'&&(r[4]||r[3])?document.getElementById(r[4]||r[3]):page==='about'&&r[1]==='acknowledgments'?document.getElementById('acknowledgments'):null;
    if(target)target.scrollIntoView({block:'start',behavior:'instant'});
  };
  requestAnimationFrame(scrollToTarget);
  typeset().then(()=>requestAnimationFrame(scrollToTarget));
}
function validateDocument(doc) {
  const obj=v=>v&&typeof v==='object'&&!Array.isArray(v);
  const str=(v,where)=>{if(v!==undefined&&(typeof v!=='string'||v.length>2000000))throw new Error('Invalid text in '+where+'.');};
  if(!obj(doc)||doc.schemaVersion!==2||doc.format!=='html'||doc.bookId!=='traceformulas-'+currentVolume.id||!obj(doc.chapters))throw new Error('The published content has an invalid volume schema.');
  str(doc.acknowledgments,'acknowledgments');
  for(const [id,c] of Object.entries(doc.chapters)) {
    const record=records.find(r=>r.id===id);if(!record||!obj(c))throw new Error('Unknown chapter or invalid chapter data: '+id);
    str(c.intro,id);
    if(c.sections!==undefined) {
      if(!obj(c.sections))throw new Error('Invalid section content.');
      for(const [s,t] of Object.entries(c.sections)){if(!record.sections.some(x=>x.id===s))throw new Error('Unknown section: '+s);str(t,s);}
    }
    for(const [field,fields] of Object.entries({videos:['title','kind','url','transcript'],comparisons:['title','book','lean','notes'],exercises:['title','question','hint','solution'],explorations:['title','url','description'],resources:['title','url']})) {
      if(c[field]===undefined)continue;
      if(!Array.isArray(c[field])||c[field].length>500)throw new Error('Invalid '+field+' list.');
      for(const row of c[field]){if(!obj(row))throw new Error('Invalid '+field+' entry.');for(const f of fields)str(row[f],field);if(field==='videos'&&row.kind!==undefined&&!['concept','proof','formalization'].includes(row.kind))throw new Error('Invalid video type.');}
    }
    if(c.formal!==undefined) {
      if(!obj(c.formal))throw new Error('Invalid formalization data.');
      for(const field of ['summary','url','declarations'])str(c.formal[field],'formalization');
      if(c.formal.status!==undefined&&!Object.hasOwn(formalStatusLabels,c.formal.status))throw new Error('Invalid formalization status.');
    }
    const refs=(list,target)=>{
      if(!Array.isArray(list)||list.length>1000||list.some(v=>typeof v!=='string'||!nodes.has(v)||v===target))throw new Error('Invalid prerequisite connection.');
    };
    if(c.prerequisites!==undefined)refs(c.prerequisites,id);
    if(c.sectionPrerequisites!==undefined) {
      if(!obj(c.sectionPrerequisites))throw new Error('Invalid section prerequisites.');
      for(const [s,ps] of Object.entries(c.sectionPrerequisites)){if(!record.sections.some(x=>x.id===s))throw new Error('Unknown section in dependency map.');refs(ps,s);}
    }
  }
  return doc;
}

function showSearch() {
  const dialog=$('#search-dialog');
  dialog.innerHTML='<div class="search-head">'+icon('search',20)+'<label class="sr-only" id="search-title" for="volume-search">Search the volume</label><input id="volume-search" type="search" placeholder="A chapter, section, or mathematical idea…" autocomplete="off"><button class="icon-button" data-action="close-dialog" aria-label="Close search">'+icon('close',18)+'</button></div><div class="search-results" id="search-results"></div><div class="search-footer">Search chapter titles, sections, and added text · Escape to close</div>';
  const input=$('#volume-search');
  function results() {
    const q=input.value.trim().toLocaleLowerCase(),found=[];
    records.forEach(r=>{
      const c=content(r.id);
      if(!q||[r.title,r.description,c.intro].join(' ').toLocaleLowerCase().includes(q))found.push({r,title:r.title,label:chapterLabel(r),href:chapterLink(r)});
      if(q)r.sections.forEach((s,i)=>{if([s.title,c.sections[s.id]||''].join(' ').toLocaleLowerCase().includes(q))found.push({r,title:s.title,label:'Section '+sectionNumber(r,i),href:chapterLink(r,'read',s.id)});});
    });
    $('#search-results').innerHTML=found.length?found.slice(0,50).map(x=>'<a class="search-result" href="'+x.href+'">'+icon('book',17)+'<span><small>'+x.label+'</small><strong>'+esc(x.title)+'</strong></span></a>').join(''):'<p class="search-empty">No matches. Try a chapter title or a shorter phrase.</p>';
  }
  input.addEventListener('input',results);results();dialog.showModal();input.focus();
}
function closeMobile() {$('#sidebar').classList.remove('open');$('#mobile-scrim').hidden=true;$('.menu-toggle')?.setAttribute('aria-expanded','false');}
document.addEventListener('click',event=>{
  if(event.target.closest('.skip-link')){event.preventDefault();$('#main').focus();$('#main').scrollIntoView({block:'start'});return;}
  const fragment=event.target.closest('.prose a[href^="#"]');
  if(fragment&&!fragment.getAttribute('href').startsWith('#/')) {
    const target=document.getElementById(fragment.getAttribute('href').slice(1));
    if(target){event.preventDefault();target.scrollIntoView({block:'start'});return;}
  }
  const link=event.target.closest('a[href^="#/"]');
  if(link){
    $('#search-dialog').close();closeMobile();
    if(link.closest('.section-nav')&&link.hash===location.hash){
      document.getElementById(route()[3])?.scrollIntoView({block:'start',behavior:'instant'});
    }
  }
  const button=event.target.closest('[data-action]');if(!button)return;
  event.preventDefault();
  const action=button.dataset.action;
  if(action==='search')showSearch();
  if(action==='close-dialog')button.closest('dialog').close();
  if(action==='map-mode'){globalMapMode=button.dataset.mode;render();}
  if(action==='menu'){const open=$('#sidebar').classList.toggle('open');$('#mobile-scrim').hidden=!open;button.setAttribute('aria-expanded',String(open));}
  if(action==='chapter-sections'){
    const list=document.getElementById(button.getAttribute('aria-controls'));
    const expanded=button.getAttribute('aria-expanded')!=='true';
    button.setAttribute('aria-expanded',String(expanded));
    list.hidden=!expanded;
    sidebarExpanded.set(button.dataset.sidebarKey,expanded);
  }
});
document.addEventListener('change',event=>{if(event.target.id==='volume-select'){const volume=series.volumes.find(v=>v.id===event.target.value);if(volume)location.href=volumeURL(volume);}if(event.target.id==='map-focus'){mapTarget=event.target.value;render();}});
document.addEventListener('keydown',event=>{
  const typing=/INPUT|TEXTAREA|SELECT/.test(document.activeElement?.tagName)||document.activeElement?.isContentEditable;
  if((event.key==='/'&&!typing)||((event.metaKey||event.ctrlKey)&&event.key==='k')){if(document.querySelector('dialog[open]'))return;event.preventDefault();showSearch();}
  if(event.key==='Escape')closeMobile();
});
$('#mobile-scrim').addEventListener('click',closeMobile);
window.addEventListener('hashchange',()=>{window.scrollTo({top:0,behavior:'instant'});render();});

async function init() {
  try {
    const catalog=await fetch('data/series.json');
    if(!catalog.ok)throw new Error('The series catalog could not be loaded.');
    series=await catalog.json();
    const selected=new URLSearchParams(location.search).get('volume')||series.defaultVolume;
    currentVolume=series.volumes.find(v=>v.id===selected);
    if(!currentVolume)throw new Error('Unknown volume: '+selected);
    const responses=await Promise.all([fetch(currentVolume.dataPath+'/outline.json'),fetch(currentVolume.dataPath+'/content.json')]);
    if(responses.some(r=>!r.ok))throw new Error('A content file could not be loaded.');
    [outline,published]=await Promise.all(responses.map(r=>r.json()));
    records=[...outline.chapters,...outline.appendices];
    for(const r of records) {
      nodes.set(r.id,{id:r.id,label:chapterLabel(r)+' · '+r.title,record:r});
      r.sections.forEach((s,i)=>nodes.set(s.id,{id:s.id,label:sectionNumber(r,i)+' · '+s.title,record:r,sectionId:s.id}));
    }
    validateDocument(published);
    render();
  }catch(e){$('#main').innerHTML='<div class="error-page"><h1>The volume could not open.</h1><p>'+esc(e.message)+'</p><p>Please reload the page. This prototype must be served from a website.</p></div>';}
}
init();
