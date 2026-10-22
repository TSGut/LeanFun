/* Run in the isolated fixture produced by test_revolver_browser.py. */
(async function () {
  var report=document.getElementById('test-report'),count=0;
  function check(ok,message){if(!ok)throw new Error(message);count++;}
  async function until(f){for(var i=0;i<150;i++){if(f())return;await new Promise(function(r){setTimeout(r,30);});}throw new Error('Timed out waiting for browser UI');}
  try {
    var api=window.RevolverSearch;
    check(!!api,'search API loaded');
    var entry=api.prepare({title:'Gegenbauer derivative',label:'thm:derivative',role:'main',status:'formalised',lean:['Polynomial.first','Polynomial.derivative_gegenbauer'],aliases:['ultraspherical'],text:'x'.repeat(900)+' tailneedle',math:'',citations:['dlmf 18.9.15'],chapter:'Families',url:'index.html#target'});
    check(api.search([entry],{q:'ultraspherical derivative'}).length===1,'family alias');
    check(api.search([entry],{q:'DLMF 18.9.15'}).length===1,'citation locator');
    check(api.search([entry],{q:'tailneedle'}).length===1,'untruncated tail');
    check(api.normalize('Clenshaw–Curtis')===api.normalize('Clenshaw-Curtis'),'hyphen normalization');
    check(api.normalize('₂F₁')==='2f1','Unicode mathematical name');
    check(api.resultURL(entry,'derivative_gegenbauer').includes('decl=Polynomial.derivative_gegenbauer'),'exact related declaration URL');
    check(api.search([entry],{q:'derivative',status:'planned'}).length===0,'independent status filter');
    var planned=api.prepare({title:'Future target',status:'planned',text:'hiddenneedle'});
    check(api.search([planned],{q:'hiddenneedle'}).length===1,'planned body-only matches remain searchable');
    await until(function(){return document.querySelector('.rv-result-count').textContent.includes('Enter a query');});
    check(document.querySelectorAll('.rv-full-results li').length===0,'landing page has no unsolicited results');
    history.pushState(null,'','?q=result');dispatchEvent(new PopStateEvent('popstate'));
    check(document.querySelectorAll('.rv-full-results li').length===40,'first result page');
    check(!document.querySelector('.rv-result-snippet'),'flattened formulas are not presented as mathematical statements');
    check(document.querySelector('.rv-pagination a').href.includes('page=2'),'next page accessible');
    history.pushState(null,'','?q=result&page=2');dispatchEvent(new PopStateEvent('popstate'));
    check(document.querySelectorAll('.rv-full-results li').length===25,'all matches reachable on second page');
    history.pushState(null,'','?role=planned');dispatchEvent(new PopStateEvent('popstate'));
    check(document.querySelectorAll('.rv-full-results li').length===1,'planned filter');
    var quick=document.querySelector('.rv-search input');quick.value='result';quick.dispatchEvent(new Event('input'));
    await until(function(){return document.querySelectorAll('.rv-search-results li').length===13;});
    check(document.querySelector('.rv-search-results .rv-search-number').textContent==='Thm. 0','numbered search suggestions');
    check(document.querySelector('.rv-all-results').textContent==='View all 65 results','quick search full-result escape');
    quick.dispatchEvent(new KeyboardEvent('keydown',{key:'ArrowDown',bubbles:true}));
    check(quick.getAttribute('aria-activedescendant')==='rv-option-1','keyboard selection');
    quick.dispatchEvent(new KeyboardEvent('keydown',{key:'Escape',bubbles:true}));
    check(quick.getAttribute('aria-expanded')==='false','escape closes disclosure');
    history.replaceState(null,'','?decl=Polynomial.derivative_gegenbauer#target');api.reveal();
    check(document.getElementById('outer').open&&document.getElementById('formal').open&&document.getElementById('related').open,'all nested disclosures opened');
    check(document.activeElement.dataset.leanName==='Polynomial.derivative_gegenbauer','matching declaration focused');
    document.getElementById('outer').open=false;dispatchEvent(new PopStateEvent('popstate'));
    check(document.getElementById('outer').open,'history navigation reveals target');
    report.textContent='PASS '+count+' browser assertions';report.dataset.result='pass';
  }catch(e){report.textContent='FAIL '+e.stack;report.dataset.result='fail';}
})();
