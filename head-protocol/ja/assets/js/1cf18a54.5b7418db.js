"use strict";(self.webpackChunkhydra_head_protocol_docs=self.webpackChunkhydra_head_protocol_docs||[]).push([[2293],{3905:(t,e,a)=>{a.d(e,{Zo:()=>u,kt:()=>m});var n=a(7294);function r(t,e,a){return e in t?Object.defineProperty(t,e,{value:a,enumerable:!0,configurable:!0,writable:!0}):t[e]=a,t}function o(t,e){var a=Object.keys(t);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(t);e&&(n=n.filter((function(e){return Object.getOwnPropertyDescriptor(t,e).enumerable}))),a.push.apply(a,n)}return a}function i(t){for(var e=1;e<arguments.length;e++){var a=null!=arguments[e]?arguments[e]:{};e%2?o(Object(a),!0).forEach((function(e){r(t,e,a[e])})):Object.getOwnPropertyDescriptors?Object.defineProperties(t,Object.getOwnPropertyDescriptors(a)):o(Object(a)).forEach((function(e){Object.defineProperty(t,e,Object.getOwnPropertyDescriptor(a,e))}))}return t}function l(t,e){if(null==t)return{};var a,n,r=function(t,e){if(null==t)return{};var a,n,r={},o=Object.keys(t);for(n=0;n<o.length;n++)a=o[n],e.indexOf(a)>=0||(r[a]=t[a]);return r}(t,e);if(Object.getOwnPropertySymbols){var o=Object.getOwnPropertySymbols(t);for(n=0;n<o.length;n++)a=o[n],e.indexOf(a)>=0||Object.prototype.propertyIsEnumerable.call(t,a)&&(r[a]=t[a])}return r}var c=n.createContext({}),s=function(t){var e=n.useContext(c),a=e;return t&&(a="function"==typeof t?t(e):i(i({},e),t)),a},u=function(t){var e=s(t.components);return n.createElement(c.Provider,{value:e},t.children)},p={inlineCode:"code",wrapper:function(t){var e=t.children;return n.createElement(n.Fragment,{},e)}},d=n.forwardRef((function(t,e){var a=t.components,r=t.mdxType,o=t.originalType,c=t.parentName,u=l(t,["components","mdxType","originalType","parentName"]),d=s(a),m=r,h=d["".concat(c,".").concat(m)]||d[m]||p[m]||o;return a?n.createElement(h,i(i({ref:e},u),{},{components:a})):n.createElement(h,i({ref:e},u))}));function m(t,e){var a=arguments,r=e&&e.mdxType;if("string"==typeof t||r){var o=a.length,i=new Array(o);i[0]=d;var l={};for(var c in e)hasOwnProperty.call(e,c)&&(l[c]=e[c]);l.originalType=t,l.mdxType="string"==typeof t?t:r,i[1]=l;for(var s=2;s<o;s++)i[s]=a[s];return n.createElement.apply(null,i)}return n.createElement.apply(null,a)}d.displayName="MDXCreateElement"},661:(t,e,a)=>{a.r(e),a.d(e,{assets:()=>c,contentTitle:()=>i,default:()=>p,frontMatter:()=>o,metadata:()=>l,toc:()=>s});var n=a(7462),r=(a(7294),a(3905));const o={slug:13,title:"13. Plutus Contracts Testing Strategy\n",authors:[],tags:["Accepted"]},i=void 0,l={permalink:"/head-protocol/ja/adr/13",source:"@site/adr/2022-01-19_013-contract-testing-strategy.md",title:"13. Plutus Contracts Testing Strategy\n",description:"Status",date:"2022-01-19T00:00:00.000Z",formattedDate:"2022\u5e741\u670819\u65e5",tags:[{label:"Accepted",permalink:"/head-protocol/ja/adr/tags/accepted"}],readingTime:1.26,truncated:!1,authors:[],frontMatter:{slug:"13",title:"13. Plutus Contracts Testing Strategy\n",authors:[],tags:["Accepted"]},prevItem:{title:"12. Top-down Test-driven Design\n",permalink:"/head-protocol/ja/adr/12"},nextItem:{title:"14. Token usage in Hydra Scripts\n",permalink:"/head-protocol/ja/adr/14"}},c={authorsImageUrls:[]},s=[{value:"Status",id:"status",level:2},{value:"Context",id:"context",level:2},{value:"Decision",id:"decision",level:2},{value:"Consequences",id:"consequences",level:2}],u={toc:s};function p(t){let{components:e,...a}=t;return(0,r.kt)("wrapper",(0,n.Z)({},u,a,{components:e,mdxType:"MDXLayout"}),(0,r.kt)("h2",{id:"status"},"Status"),(0,r.kt)("p",null,"Accepted"),(0,r.kt)("h2",{id:"context"},"Context"),(0,r.kt)("ul",null,(0,r.kt)("li",{parentName:"ul"},"We are implementing our custom (",(0,r.kt)("a",{parentName:"li",href:"/adr/10"},"Direct"),") interaction w/ Cardano blockchain and not using the PAB nor the ",(0,r.kt)("inlineCode",{parentName:"li"},"Contract")," monad to define off-chain contract code"),(0,r.kt)("li",{parentName:"ul"},"This implies we cannot use the ",(0,r.kt)("a",{parentName:"li",href:"https://github.com/input-output-hk/plutus-apps/blob/main/plutus-contract/src/Plutus/Contract/Test.hs"},"official")," testing framework for Contracts which relies on ",(0,r.kt)("inlineCode",{parentName:"li"},"Contract")," monad and emulator traces nor the ",(0,r.kt)("a",{parentName:"li",href:"https://plutus-apps.readthedocs.io/en/latest/plutus/tutorials/contract-testing.html"},"QuickCheck based framework")),(0,r.kt)("li",{parentName:"ul"},"We want to follow our ",(0,r.kt)("a",{parentName:"li",href:"/adr/12"},"Test-Driven Development")," approach for contracts as this is a critical part of Hydra"),(0,r.kt)("li",{parentName:"ul"},"On-Chain Validators need not only to be correct and functional, but also secure and hardened against malicious parties")),(0,r.kt)("h2",{id:"decision"},"Decision"),(0,r.kt)("p",null,(0,r.kt)("em",{parentName:"p"},"Therefore")),(0,r.kt)("ul",null,(0,r.kt)("li",{parentName:"ul"},"We test-drive single contracts code using ",(0,r.kt)("em",{parentName:"li"},"Mutation-Based Property Testing")),(0,r.kt)("li",{parentName:"ul"},"Contracts are tested through the construction of actual ",(0,r.kt)("em",{parentName:"li"},"transactions")," and running phase-2 ledger validation process"),(0,r.kt)("li",{parentName:"ul"},'We start from a "healthy" transaction, that\'s expected to be correct and stay so'),(0,r.kt)("li",{parentName:"ul"},"Contract code is initially ",(0,r.kt)("inlineCode",{parentName:"li"},"const True")," function that validates any transaction"),(0,r.kt)("li",{parentName:"ul"},"We flesh the contract's code piecemeal through the introduction of ",(0,r.kt)("em",{parentName:"li"},"Mutations")," that turn a healthy transaction into an expectedly invalid one"),(0,r.kt)("li",{parentName:"ul"},"We gradually build a set of combinators and generators that make it easier to mutate arbitrarily transactions, and combine those mutations")),(0,r.kt)("h2",{id:"consequences"},"Consequences"),(0,r.kt)("ul",null,(0,r.kt)("li",{parentName:"ul"},"We make the contracts' ",(0,r.kt)("em",{parentName:"li"},"Threat model"),"  explicit through the tests we write, which should help future auditors' work"),(0,r.kt)("li",{parentName:"ul"},"We'll need an additional layer of tests to exercise the Hydra OCV State Machine through ",(0,r.kt)("em",{parentName:"li"},"sequence of transactions"),". This could be implemented using ",(0,r.kt)("a",{parentName:"li",href:"https://github.com/input-output-hk/plutus-apps/tree/main/quickcheck-dynamic"},"quickcheck-dynamic")," library, or other tools that are currently being developed by the Cardano community")))}p.isMDXComponent=!0}}]);