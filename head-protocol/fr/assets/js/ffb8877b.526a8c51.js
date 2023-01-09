"use strict";(self.webpackChunkhydra_head_protocol_docs=self.webpackChunkhydra_head_protocol_docs||[]).push([[1719],{3905:(e,t,r)=>{r.d(t,{Zo:()=>u,kt:()=>m});var a=r(7294);function n(e,t,r){return t in e?Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}):e[t]=r,e}function o(e,t){var r=Object.keys(e);if(Object.getOwnPropertySymbols){var a=Object.getOwnPropertySymbols(e);t&&(a=a.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),r.push.apply(r,a)}return r}function i(e){for(var t=1;t<arguments.length;t++){var r=null!=arguments[t]?arguments[t]:{};t%2?o(Object(r),!0).forEach((function(t){n(e,t,r[t])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(r)):o(Object(r)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(r,t))}))}return e}function l(e,t){if(null==e)return{};var r,a,n=function(e,t){if(null==e)return{};var r,a,n={},o=Object.keys(e);for(a=0;a<o.length;a++)r=o[a],t.indexOf(r)>=0||(n[r]=e[r]);return n}(e,t);if(Object.getOwnPropertySymbols){var o=Object.getOwnPropertySymbols(e);for(a=0;a<o.length;a++)r=o[a],t.indexOf(r)>=0||Object.prototype.propertyIsEnumerable.call(e,r)&&(n[r]=e[r])}return n}var s=a.createContext({}),p=function(e){var t=a.useContext(s),r=t;return e&&(r="function"==typeof e?e(t):i(i({},t),e)),r},u=function(e){var t=p(e.components);return a.createElement(s.Provider,{value:t},e.children)},c={inlineCode:"code",wrapper:function(e){var t=e.children;return a.createElement(a.Fragment,{},t)}},d=a.forwardRef((function(e,t){var r=e.components,n=e.mdxType,o=e.originalType,s=e.parentName,u=l(e,["components","mdxType","originalType","parentName"]),d=p(r),m=n,h=d["".concat(s,".").concat(m)]||d[m]||c[m]||o;return r?a.createElement(h,i(i({ref:t},u),{},{components:r})):a.createElement(h,i({ref:t},u))}));function m(e,t){var r=arguments,n=t&&t.mdxType;if("string"==typeof e||n){var o=r.length,i=new Array(o);i[0]=d;var l={};for(var s in t)hasOwnProperty.call(t,s)&&(l[s]=t[s]);l.originalType=e,l.mdxType="string"==typeof e?e:n,i[1]=l;for(var p=2;p<o;p++)i[p]=r[p];return a.createElement.apply(null,i)}return a.createElement.apply(null,r)}d.displayName="MDXCreateElement"},4914:(e,t,r)=>{r.r(t),r.d(t,{assets:()=>s,contentTitle:()=>i,default:()=>c,frontMatter:()=>o,metadata:()=>l,toc:()=>p});var a=r(7462),n=(r(7294),r(3905));const o={},i="Troubleshooting",l={unversionedId:"getting-started/troubleshooting",id:"getting-started/troubleshooting",title:"Troubleshooting",description:"Known issues",source:"@site/docs/getting-started/troubleshooting.md",sourceDirName:"getting-started",slug:"/getting-started/troubleshooting",permalink:"/head-protocol/fr/docs/getting-started/troubleshooting",editUrl:"https://github.com/input-output-hk/hydra/tree/master/docs/docs/getting-started/troubleshooting.md",tags:[],version:"current",frontMatter:{},sidebar:"defaultSidebar",previous:{title:"Glossary",permalink:"/head-protocol/fr/docs/getting-started/glossary"},next:{title:"Biblioth\xe8ques Haskell",permalink:"/head-protocol/fr/docs/haskell_packages"}},s={},p=[{value:"Known issues",id:"known-issues",level:2},{value:"hydra-node",id:"hydra-node",level:3},{value:"hydra-tui",id:"hydra-tui",level:3}],u={toc:p};function c(e){let{components:t,...r}=e;return(0,n.kt)("wrapper",(0,a.Z)({},u,r,{components:t,mdxType:"MDXLayout"}),(0,n.kt)("h1",{id:"troubleshooting"},"Troubleshooting"),(0,n.kt)("h2",{id:"known-issues"},"Known issues"),(0,n.kt)("h3",{id:"hydra-node"},"hydra-node"),(0,n.kt)("ul",null,(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"AcquireFailurePointNotOnChain"),(0,n.kt)("ul",{parentName:"li"},(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"It ocurs when you attempt to start a head using a point in the past too old (exceeding ",(0,n.kt)("strong",{parentName:"p"},"k")," limit).")),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Reference: ",(0,n.kt)("a",{parentName:"p",href:"https://github.com/input-output-hk/hydra/issues/439"},"issue #439")," AcquireFailurePointTooOld when ",(0,n.kt)("inlineCode",{parentName:"p"},"--start-chain-from")," point is past ",(0,n.kt)("strong",{parentName:"p"},"k"),".")),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Workaround: Restart your node fresh, without state. For that you need to remove your persistance dir and restart the hydra-node.")))),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Hydra node crashes after a fork"),(0,n.kt)("ul",{parentName:"li"},(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"It ocurs during a fork and expects the operator to restart its hydra-node.")),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Reference: ",(0,n.kt)("a",{parentName:"p",href:"https://github.com/input-output-hk/hydra/issues/560"},"issue #560")," Hydra node crashed after a fork.")),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Workaround: Restarting your node should be enough to come back to live. Beware, if you wait to long to restart it then you may fall under ",(0,n.kt)("inlineCode",{parentName:"p"},"QueryAcquireException AcquireFailurePointTooOld")," and will require you to restart without state.")))),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"The current transaction size has a limit of ~16KB. This causes the following inconveniences:"),(0,n.kt)("ul",{parentName:"li"},(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"The protocol can only handle a maximum number of participants by Head. See ",(0,n.kt)("a",{parentName:"p",href:"https://hydra.family/head-protocol/benchmarks/transaction-cost/#cost-of-collectcom-transaction"},"cost of collectcom transaction")," or the ",(0,n.kt)("inlineCode",{parentName:"p"},"hydra-node")," will inform you of the current configured maximum when trying to configure too many peers.")),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Only one or no utxo can be committed by each party to a Head.")),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"The head cannot be finalized if holding more than ~100 assets. See ",(0,n.kt)("a",{parentName:"p",href:"https://hydra.family/head-protocol/benchmarks/transaction-cost/#cost-of-fanout-transaction"},"cost of fanout transaction")," for latest numbers.")))),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Not an issue, but a workaround: The internal wallet of ",(0,n.kt)("inlineCode",{parentName:"p"},"hydra-node"),' requires a UTXO to be marked as "fuel" to drive the Hydra protocol transactions. See ',(0,n.kt)("a",{parentName:"p",href:"https://hydra.family/head-protocol/docs/getting-started/demo/with-docker/#seeding-the-network"},"user manual"),"."))),(0,n.kt)("h3",{id:"hydra-tui"},"hydra-tui"),(0,n.kt)("ul",null,(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"TUI crashes when user tries to post a new transaction wihout any UTXO remaining.")),(0,n.kt)("li",{parentName:"ul"},(0,n.kt)("p",{parentName:"li"},"Recipient addresses to send money to in the TUI are inferred from the current UTXO set. If a party does not commit a UTXO or consumes all its UTXO in a Head, it won't be able to send or receive anything anymore."))))}c.isMDXComponent=!0}}]);