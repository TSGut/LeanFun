/* LeanFun RevOLVER: dark mode, logo, cover image and dependency-graph zoom. */
(function () {
  var KEY = 'revolver-theme';
  var root = document.documentElement;
  var media = window.matchMedia ? window.matchMedia('(prefers-color-scheme: dark)') : null;

  function stored() {
    try { return window.localStorage.getItem(KEY); } catch (e) { return null; }
  }
  function store(t) {
    try { window.localStorage.setItem(KEY, t); } catch (e) { /* private mode */ }
  }
  function preferred() {
    return stored() || (media && media.matches ? 'dark' : 'light');
  }
  function apply(theme) {
    root.setAttribute('data-theme', theme);
    var b = document.getElementById('rv-theme-toggle');
    if (b) {
      b.textContent = theme === 'dark' ? '☀' : '☾';
      b.title = theme === 'dark' ? 'Switch to light mode' : 'Switch to dark mode';
      b.setAttribute('aria-label', b.title);
    }
  }

  // The dependency-graph page does not load the book stylesheet by itself.
  if (!document.querySelector('link[href$="revolver.css"]')) {
    var css = document.createElement('link');
    css.rel = 'stylesheet';
    css.href = 'styles/revolver.css';
    document.head.appendChild(css);
  }

  // Shared search engine: full mathematical text, aliases, citations and exact names.
  function normalize(s) {
    return String(s || '').normalize('NFKD').replace(/[\u0300-\u036f]/g, '')
      .toLowerCase().replace(/[‐‑–—−-]/g, ' ').replace(/\s+/g, ' ').trim();
  }
  function prepare(e) {
    e._title = normalize(e.title);
    e._names = (e.lean || []).map(normalize);
    e._short = e._names.map(function (x) { return x.split('.').pop(); });
    e._label = normalize(e.label);
    e._alias = normalize((e.aliases || []).join(' '));
    e._body = normalize([e.chapter, e.section, e.text, e.math,
      (e.citations || []).join(' ')].join(' '));
    return e;
  }
  function score(e, query) {
    var q = normalize(query);
    if (!q) return 1;
    if (e._names.indexOf(q) >= 0 || e._short.indexOf(q) >= 0 || e._label === q) return 1000;
    var s = 0, words = q.split(' ');
    for (var i = 0; i < words.length; i++) {
      var w = words[i];
      if (e._title.indexOf(w) >= 0) s += 8;
      else if (e._alias.indexOf(w) >= 0) s += 7;
      else if (e._names.join(' ').indexOf(w) >= 0) s += 4;
      else if (e._label.indexOf(w) >= 0) s += 3;
      else if (e._body.indexOf(w) >= 0) s += 1;
      else return 0;
    }
    if (e._title === q) s += 20;
    return Math.max(1, s + (e.role === 'main' ? 4 : 0) - (e.status === 'planned' ? 2 : 0) + 1);
  }
  function search(index, state) {
    return index.filter(function (e) {
      return (!state.topic || (e.topics || []).indexOf(state.topic) >= 0) &&
        (!state.role || e.role === state.role) &&
        (!state.chapter || e.chapter_label === state.chapter) &&
        (!state.status || e.status === state.status || e.review === state.status);
    }).map(function (e, i) { return {entry:e, rank:score(e, state.q), order:i}; })
      .filter(function (x) { return x.rank > 0; })
      .sort(function (a,b) { return b.rank-a.rank || a.order-b.order; })
      .map(function (x) { return x.entry; });
  }
  var indexPromise;
  function loadIndex() {
    if (!indexPromise) indexPromise = fetch('search-index.json').then(function (r) {
      if (!r.ok) throw new Error('Search index unavailable (' + r.status + ')');
      return r.json();
    }).then(function (a) { return a.map(prepare); }).catch(function (err) {
      indexPromise = null; throw err;
    });
    return indexPromise;
  }
  function resultURL(e, query) {
    var q = normalize(query), decl = (e.lean || []).find(function (n) {
      return normalize(n) === q || normalize(n.split('.').pop()) === q;
    });
    if (!decl) return e.url;
    var u = new URL(e.url, window.location.href);
    u.searchParams.set('decl', decl);
    return u.pathname.split('/').pop()+u.search+u.hash;
  }
  function element(tag, cls, text) {
    var n=document.createElement(tag); if (cls) n.className=cls;
    if (text !== undefined) n.textContent=text; return n;
  }
  function referenceURL(state) {
    var p=new URLSearchParams();
    Object.keys(state).forEach(function (k) { if (state[k]) p.set(k,state[k]); });
    return 'reference.html'+(p.toString()?'?'+p.toString():'');
  }
  function resultLink(e,q) {
    var a=element('a','');a.href=resultURL(e,q);
    var heading=element('span','rv-search-head');
    heading.appendChild(element('span','rv-search-title',e.title || e.label));
    if(e.ref){
      var names={Definition:'Def.',Theorem:'Thm.',Lemma:'Lemma',Proposition:'Prop.',Corollary:'Cor.'};
      heading.appendChild(element('span','rv-search-number',(names[e.kind]||e.kind||'')+' '+e.ref));
    }
    a.appendChild(heading);
    a.appendChild(element('span','rv-search-meta',[e.chapter,e.section,e.role,
      e.status === 'planned' ? 'PLANNED TARGET' : e.status,
      e.review === 'reviewed-current' ? 'human-reviewed' : e.review === 'stale' ? 'review stale' : ''].filter(Boolean).join(' · ')));
    return a;
  }
  function searchBox() {
    var wrap=element('div','rv-search'), input=element('input'), list=element('ol','rv-search-results');
    var message=element('div','rv-search-message');message.setAttribute('role','status');
    input.type='search';input.placeholder='Search /';input.autocomplete='off';
    input.setAttribute('aria-label','Search every result');input.setAttribute('role','combobox');
    input.setAttribute('aria-autocomplete','list');input.setAttribute('aria-controls','rv-quick-results');
    input.setAttribute('aria-expanded','false');list.id='rv-quick-results';list.setAttribute('role','listbox');
    list.hidden=true;wrap.append(input,list,message);
    var active=-1,links=[],serial=0;
    function hide() {list.hidden=true;input.setAttribute('aria-expanded','false');input.removeAttribute('aria-activedescendant');}
    function choose(i) {active=i;links.forEach(function (a,j) {a.parentNode.classList.toggle('active',i===j);a.setAttribute('aria-selected',i===j?'true':'false');});
      if (links[i]) input.setAttribute('aria-activedescendant',links[i].id);}
    function update() {
      var q=input.value.trim(),ticket=++serial;list.replaceChildren();links=[];hide();
      if (!q) {message.textContent='';return;}
      message.textContent='Loading search…';
      loadIndex().then(function (index) {
        if (ticket!==serial) return;
        var matches=search(index,{q:q});message.textContent=matches.length+' results, including collapsed material';
        matches.slice(0,12).forEach(function (e) {var li=element('li'),a=resultLink(e,q);li.appendChild(a);list.appendChild(li);links.push(a);});
        var li=element('li'),all=element('a','rv-all-results','View all '+matches.length+' results');
        all.href=referenceURL({q:q});li.appendChild(all);list.appendChild(li);links.push(all);
        links.forEach(function (a,i) {a.id='rv-option-'+i;a.setAttribute('role','option');});
        list.hidden=false;input.setAttribute('aria-expanded','true');choose(0);
      }).catch(function () {if(ticket===serial) message.textContent='Search could not load. Retry by typing, or open Advanced search.';});
    }
    input.addEventListener('input',update);
    input.addEventListener('focus',function () {if(input.value) update();});
    input.addEventListener('keydown',function (ev) {
      if ((ev.key==='ArrowDown'||ev.key==='ArrowUp') && links.length && !list.hidden) {
        ev.preventDefault();choose((active+(ev.key==='ArrowDown'?1:links.length-1))%links.length);
      } else if(ev.key==='Enter'&&links[active]&&!list.hidden) {ev.preventDefault();window.location.href=links[active].href;}
      else if(ev.key==='Escape') {serial++;hide();message.textContent='';}
    });
    document.addEventListener('click',function(ev){if(!wrap.contains(ev.target)){hide();message.textContent='';}});
    document.addEventListener('keydown',function(ev){var t=ev.target;if(ev.key==='/'&&!t.isContentEditable&&!/INPUT|TEXTAREA|SELECT/.test(t.tagName)){ev.preventDefault();input.focus();}});
    return wrap;
  }
  function referencePage() {
    var host=document.getElementById('rv-reference-search');if(!host)return;
    var form=element('form','rv-filter-form'),input=element('input');input.type='search';input.name='q';input.placeholder='Formula, family, citation or Lean name';
    var label=element('label','','Search all material');label.appendChild(input);form.appendChild(label);
    var selects={};[['topic','Topic'],['role','Level'],['status','Status']].forEach(function(pair){
      var l=element('label','',pair[1]),sel=element('select');sel.name=pair[0];sel.appendChild(new Option(pair[0]==='status'?'All statuses':'All '+pair[1].toLowerCase()+'s',''));l.appendChild(sel);form.appendChild(l);selects[pair[0]]=sel;
    });
    var button=element('button','','Search');button.type='submit';form.appendChild(button);
    var reset=element('a','','Clear filters');reset.href='reference.html';form.appendChild(reset);
    var info=element('p','rv-result-count');info.setAttribute('role','status');
    var results=element('ol','rv-full-results'),pager=element('nav','rv-pagination');pager.setAttribute('aria-label','Search result pages');
    host.append(form,info,results,pager);
    info.textContent='Loading complete index…';
    loadIndex().then(function(index){
      var values={topic:Array.from(new Set(index.flatMap(function(e){return e.topics||[];}))).sort(),role:['main','reference','supporting','foundation','planned'],status:['formalised','imported','planned','reviewed-current','stale']};
      var captions={main:'Main results',reference:'Reference details',supporting:'Supporting results',foundation:'Formal foundations',planned:'Planned targets',formalised:'Formalised',imported:'Imported results','reviewed-current':'Human-reviewed (current)',stale:'Human review stale'};
      Object.keys(values).forEach(function(k){values[k].forEach(function(v){selects[k].appendChild(new Option(captions[v]||v,v));});});
      function render() {
        var p=new URLSearchParams(location.search),state={q:p.get('q')||'',topic:p.get('topic')||'',role:p.get('role')||'',status:p.get('status')||'',chapter:p.get('chapter')||''};
        input.value=state.q;Object.keys(selects).forEach(function(k){selects[k].value=state[k];});
        results.replaceChildren();pager.replaceChildren();
        if(!Object.values(state).some(function(v){return v.trim();})){
          info.textContent='Enter a query or choose a filter. Search includes collapsed results.';
          return;
        }
        var matches=search(index,state),size=40,total=Math.max(1,Math.ceil(matches.length/size));
        var page=Math.min(total,Math.max(1,parseInt(p.get('page'),10)||1));
        results.replaceChildren();pager.replaceChildren();results.start=(page-1)*size+1;
        info.textContent=matches.length+' results · page '+page+' of '+total+(state.chapter?' · chapter filter active':'')+'. Collapsed material is included. Open a result for its full statement and hypotheses.';
        matches.slice((page-1)*size,page*size).forEach(function(e){
          var li=element('li');li.appendChild(resultLink(e,state.q));
          // Plain text flattens fractions and indices incorrectly. Keep full
          // text searchable, but show mathematics only at its typeset source.
          if((e.citations||[]).length)li.appendChild(element('small','',e.citations.join(' · ')));
          results.appendChild(li);
        });
        if(!matches.length)results.appendChild(element('li','','No matching results. Try a family name, a shorter phrase or clear the filters.'));
        [page-1,page+1].forEach(function(n){if(n<1||n>total)return;var a=element('a','',n<page?'Previous results':'Next results');a.href=referenceURL(Object.assign({},state,{page:n}));pager.appendChild(a);});
      }
      form.addEventListener('submit',function(ev){ev.preventDefault();var state={q:input.value.trim()};Object.keys(selects).forEach(function(k){state[k]=selects[k].value;});
        // Submitting new criteria intentionally clears a chapter-only shortcut.
        history.pushState(null,'',referenceURL(state));render();});
      window.addEventListener('popstate',render);render();
    }).catch(function(){info.textContent='The search index could not load. Reload to retry; try again shortly.';});
  }
  function reveal() {
    var id;try{id=decodeURIComponent(location.hash.slice(1));}catch(e){return;}
    if(!id)return;
    var target=document.getElementById(id);if(!target)return;
    var decl=new URLSearchParams(location.search).get('decl');
    if(decl){var match=Array.from(target.querySelectorAll('[data-lean-name]')).find(function(n){return n.dataset.leanName===decl;});if(match)target=match;}
    for(var p=target.parentElement;p;p=p.parentElement)if(p.tagName==='DETAILS')p.open=true;
    if(target.tagName==='DETAILS')target.open=true;
    document.querySelectorAll('.rv-target').forEach(function(n){n.classList.remove('rv-target');});
    target.classList.add('rv-target');target.setAttribute('tabindex','-1');target.focus({preventScroll:true});target.scrollIntoView({block:'start'});
  }
  function legacyNavigation() {
    var file=location.pathname.split('/').pop()||'index.html';
    fetch('legacy-urls.json').then(function(r){if(!r.ok)return {};return r.json();}).then(function(map){
      var key=file+decodeURIComponent(location.hash),dest=map[key]||(!location.hash&&map[file]);
      if(dest){var u=new URL(dest,location.href);u.search=location.search;location.replace(u.href);}else reveal();
    }).catch(reveal);
  }
  window.RevolverSearch={normalize:normalize,prepare:prepare,search:search,resultURL:resultURL,reveal:reveal};
  window.addEventListener('hashchange',legacyNavigation);
  window.addEventListener('popstate',reveal);
  document.addEventListener('click',function(ev){var a=ev.target.closest('a');if(a&&a.hash&&a.pathname===location.pathname)setTimeout(reveal,0);});
  referencePage();legacyNavigation();


  // Corner controls: theme toggle and the small logo.
  var header = document.querySelector('body > header');
  if (header) {
    // Project-status warning in the top bar, on every page; remove as the project matures.
    var warning = document.createElement('div');
    warning.className = 'rv-alpha-warning';
    warning.setAttribute('role', 'note');
    warning.innerHTML = '<strong>Warning:</strong> This project is in experimental alpha state, ' +
      'this warning will be removed as the project matures.';
    header.appendChild(warning);

    var corner = document.createElement('div');
    corner.className = 'rv-corner';
    var toggle = document.createElement('button');
    toggle.id = 'rv-theme-toggle';
    toggle.type = 'button';
    toggle.addEventListener('click', function () {
      var next = root.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
      store(next);
      apply(next);
    });
    var home = document.createElement('a');
    home.href = 'index.html';
    home.className = 'rv-logo-link';
    var logo = document.createElement('img');
    logo.src = 'revolver-logo-128.png';
    logo.alt = 'LeanFun RevOLVER';
    logo.className = 'rv-logo';
    home.appendChild(logo);
    corner.appendChild(searchBox());
    var reference = element('a','rv-reference-link','Advanced search'); reference.href='reference.html'; corner.appendChild(reference);
    var version = document.querySelector('meta[name="rv-version"]');
    if (version) {
      var versionUrl = document.querySelector('meta[name="rv-version-url"]');
      var label = document.createElement(versionUrl && versionUrl.content ? 'a' : 'span');
      label.className = 'rv-version';
      label.textContent = version.content;
      if (label.tagName === 'A') {
        label.href = versionUrl.content;
        label.title = 'The LeanFun version this book was built from';
      }
      corner.appendChild(label);
    }
    corner.appendChild(toggle);
    corner.appendChild(home);
    header.appendChild(corner);
    // The corner is absolutely positioned; keep the title and warning clear of it.
    var reserve = function () { header.style.paddingRight = (corner.offsetWidth + 24) + 'px'; };
    reserve();
    window.addEventListener('resize', reserve);
  }
  apply(preferred());
  if (media && media.addEventListener) {
    media.addEventListener('change', function () { if (!stored()) apply(preferred()); });
  }

  // Cover page: the large logo above the title.
  var title = document.querySelector('.titlepage');
  if (title) {
    var cover = document.createElement('img');
    cover.src = 'revolver-logo-512.png';
    cover.alt = 'LeanFun RevOLVER logo';
    cover.className = 'rv-cover-logo';
    title.insertBefore(cover, title.firstChild);
  }

  // Every page: link back to the LeanFun repository, beside the navigation arrows.
  var repo = document.querySelector('meta[name="rv-repository"]');
  var nav = document.querySelector('nav.prev_up_next');
  if (repo && nav) {
    var link = document.createElement('a');
    link.href = repo.getAttribute('content');
    link.className = 'rv-repo-link';
    link.title = 'LeanFun source repository on GitHub';
    link.innerHTML = '<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">' +
      '<path fill="currentColor" d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17' +
      '.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15' +
      '-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78' +
      '-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64' +
      '-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51' +
      '.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2' +
      ' 0 .21.15.46.55.38A8.013 8.013 0 0016 8c0-4.42-3.58-8-8-8z"/></svg>' +
      '<span>LeanFun on GitHub</span>';
    nav.insertBefore(link, nav.firstChild);
  }

  // Dependency graph: on-page zoom controls.
  var graph = document.getElementById('graph');
  if (graph && window.d3) {
    var controls = document.createElement('div');
    controls.className = 'rv-zoom';
    function zoomButton(label, title, action) {
      var b = document.createElement('button');
      b.type = 'button';
      b.textContent = label;
      b.title = title;
      b.setAttribute('aria-label', title);
      b.addEventListener('click', action);
      controls.appendChild(b);
    }
    function viz() {
      var g = window.d3.select('#graph').graphviz();
      return g && g.zoomSelection() ? g : null;
    }
    function scale(k) {
      var g = viz();
      if (g) g.zoomSelection().transition().duration(250).call(g.zoomBehavior().scaleBy, k);
    }
    zoomButton('+', 'Zoom in', function () { scale(1.5); });
    zoomButton('−', 'Zoom out', function () { scale(1 / 1.5); });
    zoomButton('⟲', 'Reset zoom', function () {
      var g = viz();
      if (g) g.resetZoom(window.d3.transition().duration(250));
    });
    graph.parentNode.insertBefore(controls, graph);

    // Header layout hook (revolver.css keeps the title and status warning apart).
    document.body.classList.add('rv-graph-page');
    // The template keeps the default scale extent [0.1, 10] relative to the fitted view,
    // too shallow to read single nodes of the full book; widen it once the graph renders.
    (function deepen(tries) {
      var g = viz();
      if (g) { g.zoomScaleExtent([0.1, 500]); g.zoomBehavior().scaleExtent([0.1, 500]); }
      else if (tries > 0) setTimeout(function () { deepen(tries - 1); }, 250);
    })(480);
    // A double-click zooms; it should not leave open the statement popup from its two clicks.
    // Capture phase: d3-zoom stops the event's propagation on the svg.
    graph.addEventListener('dblclick', function () {
      var statements = document.getElementById('statements');
      if (statements) statements.style.display = 'none';
    }, true);
  }
})();
