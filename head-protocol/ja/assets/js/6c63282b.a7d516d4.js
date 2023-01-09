"use strict";(self.webpackChunkhydra_head_protocol_docs=self.webpackChunkhydra_head_protocol_docs||[]).push([[1285],{3905:(e,t,n)=>{n.d(t,{Zo:()=>c,kt:()=>u});var a=n(7294);function i(e,t,n){return t in e?Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!0}):e[t]=n,e}function o(e,t){var n=Object.keys(e);if(Object.getOwnPropertySymbols){var a=Object.getOwnPropertySymbols(e);t&&(a=a.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),n.push.apply(n,a)}return n}function r(e){for(var t=1;t<arguments.length;t++){var n=null!=arguments[t]?arguments[t]:{};t%2?o(Object(n),!0).forEach((function(t){i(e,t,n[t])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(n)):o(Object(n)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(n,t))}))}return e}function l(e,t){if(null==e)return{};var n,a,i=function(e,t){if(null==e)return{};var n,a,i={},o=Object.keys(e);for(a=0;a<o.length;a++)n=o[a],t.indexOf(n)>=0||(i[n]=e[n]);return i}(e,t);if(Object.getOwnPropertySymbols){var o=Object.getOwnPropertySymbols(e);for(a=0;a<o.length;a++)n=o[a],t.indexOf(n)>=0||Object.prototype.propertyIsEnumerable.call(e,n)&&(i[n]=e[n])}return i}var s=a.createContext({}),p=function(e){var t=a.useContext(s),n=t;return e&&(n="function"==typeof e?e(t):r(r({},t),e)),n},c=function(e){var t=p(e.components);return a.createElement(s.Provider,{value:t},e.children)},d={inlineCode:"code",wrapper:function(e){var t=e.children;return a.createElement(a.Fragment,{},t)}},m=a.forwardRef((function(e,t){var n=e.components,i=e.mdxType,o=e.originalType,s=e.parentName,c=l(e,["components","mdxType","originalType","parentName"]),m=p(n),u=i,h=m["".concat(s,".").concat(u)]||m[u]||d[u]||o;return n?a.createElement(h,r(r({ref:t},c),{},{components:n})):a.createElement(h,r({ref:t},c))}));function u(e,t){var n=arguments,i=t&&t.mdxType;if("string"==typeof e||i){var o=n.length,r=new Array(o);r[0]=m;var l={};for(var s in t)hasOwnProperty.call(t,s)&&(l[s]=t[s]);l.originalType=e,l.mdxType="string"==typeof e?e:i,r[1]=l;for(var p=2;p<o;p++)r[p]=n[p];return a.createElement.apply(null,r)}return a.createElement.apply(null,n)}m.displayName="MDXCreateElement"},8577:(e,t,n)=>{n.r(t),n.d(t,{assets:()=>s,contentTitle:()=>r,default:()=>d,frontMatter:()=>o,metadata:()=>l,toc:()=>p});var a=n(7462),i=(n(7294),n(3905));const o={slug:20,title:"20. Handling time\n",authors:[],tags:["Accepted"]},r=void 0,l={permalink:"/head-protocol/ja/adr/20",source:"@site/adr/2022-08-02_020-handling-time.md",title:"20. Handling time\n",description:"Status",date:"2022-08-02T00:00:00.000Z",formattedDate:"2022\u5e748\u67082\u65e5",tags:[{label:"Accepted",permalink:"/head-protocol/ja/adr/tags/accepted"}],readingTime:3.55,truncated:!1,authors:[],frontMatter:{slug:"20",title:"20. Handling time\n",authors:[],tags:["Accepted"]},prevItem:{title:"19. Use of reference scripts\n",permalink:"/head-protocol/ja/adr/19"},nextItem:{title:"21. Bounded transaction validity on Hydra protocol transactions\n",permalink:"/head-protocol/ja/adr/21"}},s={authorsImageUrls:[]},p=[{value:"Status",id:"status",level:2},{value:"Context",id:"context",level:2},{value:"Decision",id:"decision",level:2},{value:"Consequences",id:"consequences",level:2}],c={toc:p};function d(e){let{components:t,...o}=e;return(0,i.kt)("wrapper",(0,a.Z)({},c,o,{components:t,mdxType:"MDXLayout"}),(0,i.kt)("h2",{id:"status"},"Status"),(0,i.kt)("p",null,"Accepted"),(0,i.kt)("h2",{id:"context"},"Context"),(0,i.kt)("ul",null,(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"The Hydra Head protocol is expected to be isomorphic to the ledger it runs on. That means, it should support the same transaction formats and (if desired) use the same ledger rules as the layer 1.")),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"Cardano is our layer 1 and its consensus layer separates time into discrete steps, where each step is called a ",(0,i.kt)("inlineCode",{parentName:"p"},"Slot"),". The network is expected to evolve strictly monotonically on this time scale and so slot numbers (",(0,i.kt)("inlineCode",{parentName:"p"},"SlotNo"),") are always increasing.")),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"The Cardano mainnet has a block scheduled every 20 seconds, although it may take longer."),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"This is because ",(0,i.kt)("inlineCode",{parentName:"li"},"slotLength = 1.0"),' and every 20th slot is "active" with ',(0,i.kt)("inlineCode",{parentName:"li"},"f = 0.05"),"."),(0,i.kt)("li",{parentName:"ul"},"The consensus protocol requires ",(0,i.kt)("inlineCode",{parentName:"li"},"k")," blocks to be produced within ",(0,i.kt)("inlineCode",{parentName:"li"},"3k/f")," slots, where ",(0,i.kt)("inlineCode",{parentName:"li"},"k = 2160")," on mainnet."))),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"Transactions on Cardano may have a validity range with a lower and upper bound given as ",(0,i.kt)("inlineCode",{parentName:"p"},"SlotNo"),".")),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"Wall-clock time can be converted to slots (and back) using an ",(0,i.kt)("inlineCode",{parentName:"p"},"EraHistory")," or ",(0,i.kt)("inlineCode",{parentName:"p"},"EpochInterpreter")," provided by the consensus layer of the cardano node. This is required as the slot lengths could change over time."),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"All past points in time since the ",(0,i.kt)("inlineCode",{parentName:"li"},"SystemStart")," can be converted."),(0,i.kt)("li",{parentName:"ul"},"Future points in time can ",(0,i.kt)("strong",{parentName:"li"},"only"),' be converted in the "safe zone", practically being at least ',(0,i.kt)("inlineCode",{parentName:"li"},"3k/f")," slots (TODO: cross check). Refer to chapter 17 ",(0,i.kt)("em",{parentName:"li"},"Time")," on the ",(0,i.kt)("a",{parentName:"li",href:"https://hydra.iohk.io/build/16997794/download/1/report.pdf"},"consensus spec")," for more details."))),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"The Hydra Head protocol allows ",(0,i.kt)("inlineCode",{parentName:"p"},"close")," and ",(0,i.kt)("inlineCode",{parentName:"p"},"contest")," transactions only up before a deadline ",(0,i.kt)("inlineCode",{parentName:"p"},"T_final"),", and ",(0,i.kt)("inlineCode",{parentName:"p"},"fanout")," transactions after the deadline."),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"In the current implementation the deadline is upper validity of ",(0,i.kt)("inlineCode",{parentName:"li"},"closed")," plus the contestation period."),(0,i.kt)("li",{parentName:"ul"},"We also consider protocol variants which push out the deadline by the contestation period on each ",(0,i.kt)("inlineCode",{parentName:"li"},"contest"),"."),(0,i.kt)("li",{parentName:"ul"},"Contestation periods may very well be longer than the stability window of the protocol. For example: 7 days, while the mainnet stability window is more like 36 hours."))),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"We have encountered two problems with handling time in the past"),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"Trying to convert wall-clock time to slots of the Head protocol deadline led to ",(0,i.kt)("inlineCode",{parentName:"li"},"PastHorizonException")," (when using very low security parameter ",(0,i.kt)("inlineCode",{parentName:"li"},"k"),")"),(0,i.kt)("li",{parentName:"ul"},"Trying to ",(0,i.kt)("inlineCode",{parentName:"li"},"fanout")," after the deadline, but before another block has been seen by the L1 ledger led to ",(0,i.kt)("inlineCode",{parentName:"li"},"OutsideValidityIntervalUTxO"),"."))),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"The second problem scenario and solution ideas are roughly visible on this whiteboard:"))),(0,i.kt)("p",null,(0,i.kt)("img",{loading:"lazy",src:n(4651).Z,width:"1005",height:"1067"})),(0,i.kt)("h2",{id:"decision"},"Decision"),(0,i.kt)("ul",null,(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"The head logic uses wall-clock time to track time and only convert to/from slots when constructing/observing transactions in the chain layer."),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"This ensures that transactions we post or see on the chain can be converted to/from slots."),(0,i.kt)("li",{parentName:"ul"},"The head logic would use ",(0,i.kt)("inlineCode",{parentName:"li"},"UTCTime")," for points in time and ",(0,i.kt)("inlineCode",{parentName:"li"},"NominalDiffTime")," for durations."),(0,i.kt)("li",{parentName:"ul"},"The chain layer converts these using the ",(0,i.kt)("inlineCode",{parentName:"li"},"SystemStart")," and ",(0,i.kt)("inlineCode",{parentName:"li"},"EraHistory")," into ",(0,i.kt)("inlineCode",{parentName:"li"},"SlotNo"),"."))),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"The chain layer informs the logic layer whenever time passed (on the chain) using a new ",(0,i.kt)("inlineCode",{parentName:"p"},"Tick")," event."),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"For the direct chain implementation, this is whenever we see a block in the chain sync protocol."),(0,i.kt)("li",{parentName:"ul"},"Per above decision, the ",(0,i.kt)("inlineCode",{parentName:"li"},"Tick")," shall contain a ",(0,i.kt)("inlineCode",{parentName:"li"},"UTCTime"),' corresponding to the new "now" as seen through the block chain.')))),(0,i.kt)("h2",{id:"consequences"},"Consequences"),(0,i.kt)("ul",null,(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"Conversion from ",(0,i.kt)("inlineCode",{parentName:"p"},"UTCTime -> SlotNo")," and vice versa stays local to the chain layer.")),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"The ",(0,i.kt)("inlineCode",{parentName:"p"},"HeadLogic")," can track chain time in its state and condition ",(0,i.kt)("inlineCode",{parentName:"p"},"ReadyToFanout")," upon seeing it pass the deadline."),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"Ensures clients only see ",(0,i.kt)("inlineCode",{parentName:"li"},"ReadyToFanout")," when a following ",(0,i.kt)("inlineCode",{parentName:"li"},"Fanout")," would be really possible."),(0,i.kt)("li",{parentName:"ul"},"Makes the ",(0,i.kt)("inlineCode",{parentName:"li"},"Delay")," effect redundant and we can remove it (only delay via reenqueue on the ",(0,i.kt)("inlineCode",{parentName:"li"},"Wait")," outcome)"))),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},"By introducing ",(0,i.kt)("inlineCode",{parentName:"p"},"Tick")," events, ",(0,i.kt)("inlineCode",{parentName:"p"},"IOSim")," will not be able to detect non-progress (deadlocks)."),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"This means we cannot rely on early exit of simulations anymore and need to determine meaningful simulation endings instead of ",(0,i.kt)("inlineCode",{parentName:"li"},"waitUntilTheEndOfTime"),"."))),(0,i.kt)("li",{parentName:"ul"},(0,i.kt)("p",{parentName:"li"},'We get a first, rough notion of time for free in our L2 and can support "timed transactions" with same resolution as the L1.'),(0,i.kt)("ul",{parentName:"li"},(0,i.kt)("li",{parentName:"ul"},"Tracking time in the state makes it trivial to provide it to the ledger when we ",(0,i.kt)("inlineCode",{parentName:"li"},"applyTransaction"),"."),(0,i.kt)("li",{parentName:"ul"},'Of course we could extend the fidelity of this feature using the system clock for "dead reckoning" between blocks. The conversion of wall clock to slot could even be configurable using an L2 ',(0,i.kt)("inlineCode",{parentName:"li"},"slotLength")," analogous to L1 (although we might not want/need this).")))))}d.isMDXComponent=!0},4651:(e,t,n)=>{n.d(t,{Z:()=>a});const a=n.p+"assets/images/020-timing-fanout-ab1b5156cfc3fa34b570aa3eec42d0dd.jpg"}}]);