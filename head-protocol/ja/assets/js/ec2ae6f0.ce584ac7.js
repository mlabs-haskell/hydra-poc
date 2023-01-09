"use strict";(self.webpackChunkhydra_head_protocol_docs=self.webpackChunkhydra_head_protocol_docs||[]).push([[488],{3905:(e,t,n)=>{n.d(t,{Zo:()=>u,kt:()=>h});var a=n(7294);function o(e,t,n){return t in e?Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!0}):e[t]=n,e}function r(e,t){var n=Object.keys(e);if(Object.getOwnPropertySymbols){var a=Object.getOwnPropertySymbols(e);t&&(a=a.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),n.push.apply(n,a)}return n}function i(e){for(var t=1;t<arguments.length;t++){var n=null!=arguments[t]?arguments[t]:{};t%2?r(Object(n),!0).forEach((function(t){o(e,t,n[t])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(n)):r(Object(n)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(n,t))}))}return e}function s(e,t){if(null==e)return{};var n,a,o=function(e,t){if(null==e)return{};var n,a,o={},r=Object.keys(e);for(a=0;a<r.length;a++)n=r[a],t.indexOf(n)>=0||(o[n]=e[n]);return o}(e,t);if(Object.getOwnPropertySymbols){var r=Object.getOwnPropertySymbols(e);for(a=0;a<r.length;a++)n=r[a],t.indexOf(n)>=0||Object.prototype.propertyIsEnumerable.call(e,n)&&(o[n]=e[n])}return o}var c=a.createContext({}),l=function(e){var t=a.useContext(c),n=t;return e&&(n="function"==typeof e?e(t):i(i({},t),e)),n},u=function(e){var t=l(e.components);return a.createElement(c.Provider,{value:t},e.children)},d={inlineCode:"code",wrapper:function(e){var t=e.children;return a.createElement(a.Fragment,{},t)}},p=a.forwardRef((function(e,t){var n=e.components,o=e.mdxType,r=e.originalType,c=e.parentName,u=s(e,["components","mdxType","originalType","parentName"]),p=l(n),h=o,m=p["".concat(c,".").concat(h)]||p[h]||d[h]||r;return n?a.createElement(m,i(i({ref:t},u),{},{components:n})):a.createElement(m,i({ref:t},u))}));function h(e,t){var n=arguments,o=t&&t.mdxType;if("string"==typeof e||o){var r=n.length,i=new Array(r);i[0]=p;var s={};for(var c in t)hasOwnProperty.call(t,c)&&(s[c]=t[c]);s.originalType=e,s.mdxType="string"==typeof e?e:o,i[1]=s;for(var l=2;l<r;l++)i[l]=n[l];return a.createElement.apply(null,i)}return a.createElement.apply(null,n)}p.displayName="MDXCreateElement"},2924:(e,t,n)=>{n.r(t),n.d(t,{assets:()=>c,contentTitle:()=>i,default:()=>d,frontMatter:()=>r,metadata:()=>s,toc:()=>l});var a=n(7462),o=(n(7294),n(3905));const r={},i="NFT Auction",s={unversionedId:"nft-auction/index",id:"nft-auction/index",title:"NFT Auction",description:"Layer 1 redeemable vouchers negotiated on layer 2.",source:"@site/use-cases/nft-auction/index.md",sourceDirName:"nft-auction",slug:"/nft-auction/",permalink:"/head-protocol/ja/use-cases/nft-auction/",editUrl:"https://github.com/input-output-hk/hydra/tree/master/docs/use-cases/nft-auction/index.md",tags:[],version:"current",frontMatter:{},sidebar:"defaultSidebar",previous:{title:"Inter-Wallet Payments",permalink:"/head-protocol/ja/use-cases/inter-wallet-payments/"}},c={},l=[],u={toc:l};function d(e){let{components:t,...r}=e;return(0,o.kt)("wrapper",(0,a.Z)({},u,r,{components:t,mdxType:"MDXLayout"}),(0,o.kt)("h1",{id:"nft-auction"},"NFT Auction"),(0,o.kt)("blockquote",null,(0,o.kt)("p",{parentName:"blockquote"},"Layer 1 redeemable vouchers negotiated on layer 2.")),(0,o.kt)("p",null,"NFT drops can be a real problem when run on L1, generating a lot of UTxO and transactions in a short amount of time, clogging the network and leading to congestion and general slowdowns. The problem seems to come not much from the NFTs themselves but from the large of number of bidding transactions people post to grab some."),(0,o.kt)("p",null,"We sketch a way to run NFT auctions inside Hydra Head that would alleviate that problem. Here is an outline of the sequence of transactions involved, both on-chain and off-chain:"),(0,o.kt)("p",null,(0,o.kt)("img",{loading:"lazy",src:n(4271).Z,width:"1809",height:"413"})),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},'The auctioneer forges some "auction tokens" (a.k.a VT) representing participation in an auction for some NFT;'),(0,o.kt)("li",{parentName:"ul"},"The auctioneer commits the ATs in a Head;"),(0,o.kt)("li",{parentName:"ul"},'The Auction ATs can be "grabbed" by bidders to bid some amounts for a given NFT auction;'),(0,o.kt)("li",{parentName:"ul"},"The bidders do not have to be Head parties",(0,o.kt)("sup",null,"1"),', they just do "normal" cardano transactions to grab a bid token and then possibly keep bidding until the auction ends;'),(0,o.kt)("li",{parentName:"ul"},"The auctioneer posts a settlement transaction that consumes all current bids at some point, producing a voucher for the NFT to be sent to Bob if he pays V2'. The voucher is only valid if produced by this script, and there might be some reserve price to ensure price does not fall below some threshold;"),(0,o.kt)("li",{parentName:"ul"},"Then Head is closed and the voucher is posted on-chain;"),(0,o.kt)("li",{parentName:"ul"},"Bob can redeem his NFT, paying V2' to the auctioneer.")),(0,o.kt)("p",null,"The auctioneer runs the risk of opening/closing a Head with the winner not reclaiming his NFT. If it does not run the head itself, it runs the risk of the Head parties rigging the auction but in the worst case, the Head is closed with someone having a voucher to claim the NFT at a reserved price, or the NFTs themselves are paid back to auctioneer."),(0,o.kt)("p",null,"The bidders run the same risk of bidding in a rigged auction but in the worst case, they can refuse to pay for the NFT. Anyhow, this setup would offer already a much better security story than all the fully custodial NFT drops done on Cardano today"),(0,o.kt)("div",{className:"admonition admonition-info alert alert--info"},(0,o.kt)("div",{parentName:"div",className:"admonition-heading"},(0,o.kt)("h5",{parentName:"div"},(0,o.kt)("span",{parentName:"h5",className:"admonition-icon"},(0,o.kt)("svg",{parentName:"span",xmlns:"http://www.w3.org/2000/svg",width:"14",height:"16",viewBox:"0 0 14 16"},(0,o.kt)("path",{parentName:"svg",fillRule:"evenodd",d:"M7 2.3c3.14 0 5.7 2.56 5.7 5.7s-2.56 5.7-5.7 5.7A5.71 5.71 0 0 1 1.3 8c0-3.14 2.56-5.7 5.7-5.7zM7 1C3.14 1 0 4.14 0 8s3.14 7 7 7 7-3.14 7-7-3.14-7-7-7zm1 3H6v5h2V4zm0 6H6v2h2v-2z"}))),"NOTES ")),(0,o.kt)("div",{parentName:"div",className:"admonition-content"},(0,o.kt)("ol",{parentName:"div"},(0,o.kt)("li",{parentName:"ol"},(0,o.kt)("p",{parentName:"li"},'In this scenario, the Head is initialised by the auctioneer. It could be a "Managed Head" or "Head-as-a-Service", e.g. The auctioneer does not run a Hydra node but uses some third-party provider to run the node. A single-party head might not seem to make much sense but in this case it\'s just a way to do Cardano transactions with smart-contracts faster than on the mainchain.')),(0,o.kt)("li",{parentName:"ol"},(0,o.kt)("p",{parentName:"li"},"This use case is ",(0,o.kt)("em",{parentName:"p"},"extracted")," from a ",(0,o.kt)("a",{parentName:"p",href:"https://github.com/input-output-hk/hydra/discussions/116"},"conversation that happened on Github"),". Have a look at the conversation for details and/or to comment."))))))}d.isMDXComponent=!0},4271:(e,t,n)=>{n.d(t,{Z:()=>a});const a=n.p+"assets/images/diagram-88da1043bf0a0e5907cfdd7633a0aa82.png"}}]);