% Formal characterization of Endurant Types in UFO
% Joao Paulo A. Almeida, Apr-2018
% Contributions from Giancarlo Guizzardi, Claudenir M. Fonseca, Daniele Porello, 
% Tiago Prince Sales, Alessander B. Benevides

% Use theorem provers at http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP

%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning instantiation and specialization

% Types are those entities that are possibly instantiated
fof(ax_dtype_, axiom, (
    ![X] : (type_(X) <=> (~world(X) & ?[W,Y] : (world(W) & iof(Y,X,W)) ) )
    )).

% Individuals are those entities that are necessarily not instantiated
fof(ax_dindividual, axiom, (
    ![X] : (individual(X) <=> (~world(X) & ![W] : (world(W) => ~?[Y] : (iof(Y,X,W)))) )
    )).
    
% We are only concerned with first-order types
fof(ax_twolevel, axiom, (
    ![X,Y,W] : (iof(X,Y,W) => (individual(X) & type_(Y) & world(W)))
    )).    

% Specialization definition
fof(ax_dspecialization, axiom, (
    ![T1,T2] :
    (specializes(T1,T2) <=> (type_(T1)&type_(T2) & 
            ![W]: (world(W)=> ![E]:(iof(E,T1,W) => iof(E,T2,W)))))
    )).

% Whenever two types have a common instance, they must share a supertype or a subtype for this instance
fof(ax_nondisjointSameTaxonomy, axiom, (
    ![T1,T2]: (![X,W]: ((iof(X,T1,W)&iof(X,T2,W)&~specializes(T1,T2)&~specializes(T2,T1))=> 
        (
            (?[T3]: (specializes(T1,T3)&specializes(T2,T3)&iof(X,T3,W)))|
            (?[T3]: (specializes(T3,T1)&specializes(T3,T2)&iof(X,T3,W)))
        )
        ))
)).
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning rigidity 

% Definition of rigid type
fof(ax_drigid, axiom, (
    ![T]: (rigid(T)<=>(type_(T) &  
                    (![X]: ((?[W]: (world(W) & iof(X,T,W))) => (![W2]: (world(W2)=>iof(X,T,W2)))))))
)).

% Definition of antirigid type
fof(ax_dantirigid, axiom, (
    ![T]: (antirigid(T)<=>(type_(T) &  
                    (![X]: ((?[W]: (world(W) & iof(X,T,W))) => (?[W2]: (world(W2)&~iof(X,T,W2)))))))
)).

% Implicit definition of semirigid type 
fof(ax_semirigid, axiom, (
    ![T]: (semirigid(T)<=>(type_(T) &  
                    ~antirigid(T) & ~rigid(T)))
)).

%%%%%%%%%%%%%%%%%%%%%%%% Concerning sortality 

% Every *individual* necessarily instantiates a kind  // imply kinds are rigid!
fof(ax_individualKindMin, axiom, (
    ![X] : (individual(X) => ?[K]:(kind(K) & ![W]: (world(W)=>iof(X,K,W))))
    )).

% Every thing instantiates at most one kind (whenever it instantiates a kind it does not 
% possible instantiate a different one 
fof(ax_individualKindMax, axiom, (
    ![X,K,W] : ( ( kind(K) & iof(X,K,W)) =>
                (~?[Z,W2]: (~(Z=K) & kind(Z) & iof(X,Z,W2))) )
    )).

% Sortals definition, sortals are those types whose instances instantiate the same kind
fof(ax_dsortal, axiom, (
    ![T] :
    ( sortal(T) <=> (type_(T) & 
                    (?[K] : (kind(K) & ![X,W]: (world(W)=>(iof(X,T,W) => iof(X,K,W) )))) )) 
    )).

% A non-sortal is a type that is not a sortal 

fof(ax_dnonsortal, axiom, (
    ![T] : ( nonsortal(T) <=> (type_(T) & ~sortal(T)) ) 
    )).


%%%%%%%%%%% Concerning the leaf elements of the taxonomy of types in UFO

% Kinds and subkinds together encompass all rigid sortals
fof(ax_kindsSubkinds, axiom, (
    ![T]: ((kind(T)|subkind(T))<=>(rigid(T)&sortal(T)))
)).

% Kind and subkind are disjoint
fof(ax_kindSubkindDisjoint, axiom, (
    ~?[T]: (kind(T)&subkind(T))
)).

% Phase and roles together encompass all antirigid sortals
fof(ax_phasesRoles, axiom, (
    ![T]: ((phase(T)|role(T))<=>(antirigid(T)&sortal(T)))
)).

% They are disjoint
fof(ax_phaseRoleDisjoint, axiom, (
    ~?[T]: (phase(T)&role(T))
)).

%%% Theorems to show that we can omit <<relatorphase>> and <<relatorrole>> as a demonstration
% (same applies to relatorsubkind, modephase, moderole, modesubkind, qualityphase, qualityrole, qualitysubkind)

% Relator phase is a phase that is applicable to relators only
fof(ax_drelatorPhase, axiom, (
    ![T]: (relatorphase(T)<=> (relatortype(T) & phase(T)))
)).

% Relator role is a role that is applicable to relators only
fof(ax_drelatorRole, axiom, (
    ![T]: (relatorrole(T)<=> (relatortype(T) & role(T)))
)).

% Semi rigid sortals are those that are semirigid and sortal
fof(ax_dsemirigidSortal, axiom, (
    ![T]: (semirigidsortal(T)<=>(semirigid(T)&sortal(T)))
)).

% Categories are those types that are rigid and non-sortals
fof(ax_dcategory, axiom, (
    ![T]: (category(T)<=>(rigid(T)&nonsortal(T)))
)).

% Mixins are those types that are semirigid and non-sortals
fof(ax_dmixin, axiom, (
    ![T]: (mixin(T)<=>(semirigid(T)&nonsortal(T)))
)).

% Phase and roles together encompass all antirigid nonsortals
fof(ax_phaseRoleMixins, axiom, (
    ![T]: ((phasemixin(T)|rolemixin(T))<=>(antirigid(T)&nonsortal(T)))
)).

% They are disjoint
fof(ax_phaseRoleMixinDisjoint, axiom, (
    ~?[T]: (phasemixin(T)&rolemixin(T))
)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning the taxonomy of endurant (individuals)

% Endurants are individuals
fof(ax_endurantsAreIndividuals, axiom, (
    ![X]: (endurant(X)=>individual(X))
)).

% Substantials and moments together encompass endurants
fof(ax_substantialsMoments, axiom, (
    ![X]: ((substantial(X)|moment(X))<=>endurant(X))
)).

% Substantial and moment are disjoint
fof(ax_substantialMomentDisjoint, axiom, (
    ~?[X]: (substantial(X)&moment(X))
)).

% Relators and intrinsic moments together encompass moments
fof(ax_relatorsIntrinsicMoments, axiom, (
    ![X]: (moment(X)<=>(relator(X)|intrinsicmoment(X)))
)).

% Relator and intrinsic moment are disjoint
fof(ax_relatorIntrinsicMomentDisjoint, axiom, (
    ~?[X]: (relator(X)&intrinsicmoment(X))
)).

% Modes and qualities together encompass intrinsic moments
fof(ax_modesQualities, axiom, (
    ![X]: (intrinsicmoment(X)<=>(mode(X)|quality(X)))
)).

% Mode and quality are disjoint
fof(ax_modeQualityDisjoint, axiom, (
    ~?[X]: (mode(X)&quality(X))
)).

%%%%%%%%%%%%%%%%%%%%%%%%%% Taxonomy of endurant types according to the ontological nature of their instances

% Endurant types are all those types whose instances are endurants
fof(ax_dendurantType, axiom, (
    ![T]: (enduranttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>endurant(X)))))
)).

% Substantial types are all those types whose instances are substantials
fof(ax_dsubstantialType, axiom, (
    ![T]: (substantialtype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>substantial(X)))))
)).

% Moment types are all those types whose instances are moments
fof(ax_dmomentType, axiom, (
    ![T]: (momenttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>moment(X)))))
)).

% Relator types are all those types whose instances are relators
fof(ax_drelatorType, axiom, (
    ![T]: (relatortype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>relator(X)))))
)).

% Mode types are all those types whose instances are modes
fof(ax_dmodeType, axiom, (
    ![T]: (modetype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>mode(X)))))
)).

% Quality types are all those types whose instances are qualities
fof(ax_dqualityType, axiom, (
    ![T]: (qualitytype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>quality(X)))))
)).

%%% Kinds are specialized according to the ontological nature of their instances

% Substantial kinds are those kinds whose instances are substantials
fof(ax_dsubstantialKind, axiom, (
    ![T]: (substantialkind(T)<=> (substantialtype(T) & kind(T)))
)).

% Relator kinds are those kinds whose instances are relators
fof(ax_drelatorKind, axiom, (
    ![T]: (relatorkind(T) <=> (relatortype(T) & kind(T))) 
)).

% Mode kinds are those kinds whose instances are modes
fof(ax_dmodeKind, axiom, (
    ![T]: (modekind(T)<=> (modetype(T) & kind(T)))
)).

% Quality kinds are those kinds whose instances are relators
fof(ax_dqualityKind, axiom, (
    ![T]: (qualitykind(T)<=> (qualitytype(T) & kind(T)))
)).

% every endurant is instance of one of the specific endurant kinds 
fof(ax_everyEndurantInstantiatesSpecificKind, axiom, (
    ![X]: (endurant(X) => (?[W,K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))& iof(X,K,W))))
)).

%%% PROVEN CONJECTURE - every endurant sortal is either a kinds, subkind, phase, role or semirigid sortal
fof(cj_categorizationEndurantSortalsComplete, conjecture, (
    ![X]: ((enduranttype(X)&sortal(X))=>(substantialkind(X)|relatorkind(X)|modekind(X)|qualitykind(X)|subkind(X)|phase(X)|role(X)|semirigidsortal(X))) 
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_substantialKind, conjecture, (
    ![T]: (substantialkind(T)=>(~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_subkind, conjecture, (
    ![T]: (subkind(T) => (~substantialkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_relatorKind, conjecture, (
    ![T]: (relatorkind(T) => (~substantialkind(T)&~subkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_modeKind, conjecture, (
    ![T]: (modekind(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_qualityKind, conjecture, (
    ![T]: (qualitykind(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_category, conjecture, (
    ![T]: (category(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_mixin, conjecture, (
    ![T]: (mixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_phase, conjecture, (
    ![T]: (phase(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_role, conjecture, (
    ![T]: (role(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~phasemixin(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_phaseMixin, conjecture, (
    ![T]: (phasemixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~rolemixin(T)))
)).

%%% PROVEN CONJECTURE - leaves of the taxonomy of endurant types are disjoint
fof(cj_endurantTypesDisjoint_roleMixin, conjecture, (
    ![T]: (rolemixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T))) 
)).

%%% PROVEN CONJECTURE - endurant types must be either kinds, subkind, phase, role, semirigid sortal, mixin, phasemixin and rolemixin
fof(cj_categorizationEndurantTypesComplete, conjecture, (
    ![X]: (enduranttype(X)=>(substantialkind(X)|relatorkind(X)|modekind(X)|qualitykind(X)|subkind(X)|phase(X)|role(X)|semirigidsortal(X)|category(X)|mixin(X)|phasemixin(X)|rolemixin(X))) 
)).

%%% PROVEN CONJECTURE - Theorem: if it is a phase and it specializes a relatorkind it is a relatorphase
fof(cj_relatorPhaseDerivation, conjecture, (
    ![T]: (relatorphase(T) <=> (phase(T) & ?[K]: (relatorkind(K) & specializes(T,K))))
)).

%%% PROVEN CONJECTURE - Theorem: T is a RelatorRole iff it is a role and it specializes a relatorkind
fof(cj_relatorRoleDerivation, conjecture, (
    ![T]: (relatorrole(T) <=> (role(T) & ?[K]: (relatorkind(K) & specializes(T,K))))
)).

%%% PROVEN CONJECTURE - Theorem: every sortal endurant type is one of the types we defined (instances have the same ontological nature)
fof(cj_sameOntologicalNature, conjecture, (
    ![T]: ((sortal(T)&enduranttype(T))=>(relatortype(T)|substantialtype(T)|modetype(T)|qualitytype(T)))
)).

%%% PROVEN CONJECTURE - the same cannot be said for the nonsortals, so the following is *NOT* a theorem, as we would expect... it is independent of this theory this is because the nonsortals can have instances of the various ontological natures
fof(cj_sameOntologicalNature, conjecture, (
    ![T]: ((nonsortal(T)&enduranttype(T))=>(relatortype(T)|substantialtype(T)|modetype(T)|qualitytype(T)))
)).

/* ------------------------------------------------------------------------- */
/* ------------------------------- CONJECTURES ----------------------------- */
/* ------------------------------------------------------------------------- */


%%% PROVEN CONJECTURE - Type/Individual partition   
fof(cj_disjointnessCompletenessTop, conjecture, (
    ![X]: (world(X)|type_(X)|individual(X)) &
    ![X]: (world(X)=>(~type_(X)&~individual(X))) &
    ~?[X]: (world(X)&type_(X)) &
    ~?[X]: (world(X)&individual(X)) &
    ~?[X]: (type_(X)&individual(X)) 
)).

%%% PROVEN CONJECTURE - Specialization is quasi-reflexive
fof(cj_specQuasiReflexive, conjecture, (
    ![X] : (type_(X)=>specializes(X,X))
)).

%%% PROVEN CONJECTURE - Specialization is transitive
fof(cj_specTransitive, conjecture, (
    ![X,Y,Z] : ((specializes(X,Y)&specializes(Y,Z))=>specializes(X,Z))
)).

%%% PROVEN CONJECTURE - Rigidity Completeness - type_s are either rigid, anti-rigid or semi-rigid
fof(cj_completenessRigidity, conjecture, (
    ![T]: (type_(T)<=>(rigid(T)|semirigid(T)|antirigid(T))) 
)).

%%% PROVEN CONJECTURE - Rigidity Disjointness
fof(cj_disjointnessRigidity, conjecture, (
    ~?[X]: ((rigid(X)&antirigid(X)) | (rigid(X)&semirigid(X)) | (semirigid(X)&antirigid(X))) 
)).

%%% PROVEN CONJECTURE - Prohibited anti-rigid specialization
fof(cj_rigidCannotSpecializeAntirigid, conjecture, (
    ~?[X,Y]: ((rigid(X)|semirigid(X))&antirigid(Y)&specializes(X,Y)) 
)).

%%% PROVEN CONJECTURE - A non-sortal is a type that is not a sortal
fof(cj_dnonsortal2, conjecture, (
    ![T] : ( (type_(T) & sortal(T))=> ~nonsortal(T) ) 
    )).
    
%%%%%% theorems

%%% PROVEN CONJECTURE - kinds are rigid
fof(cj_kindsAreRigid, conjecture, (
    ![K]: (kind(K)=>rigid(K)) 
)).

%%% PROVEN CONJECTURE - kinds are disjoint
fof(cj_kindsAreDisjoint, conjecture, (
    ![X,Y] : ( (kind(X)&kind(Y)&~(X=Y)) => (![W]: (world(W) => ~?[Z]:( iof(Z,X,W)&iof(Z,Y,W)))))
)).
    
%%% PROVEN CONJECTURE - kinds are sortals
fof(cj_kindsAreSortals, conjecture, (
    ![T] : (kind(T)=>sortal(T))
)).

%%% PROVEN CONJECTURE - sortals specialize one kind
fof(cj_sortalsSpecializeOneKindMin, conjecture, (
    ![X] : (sortal(X)=>?[K]:(kind(K)&specializes(X,K)))
)).

%%% PROVEN CONJECTURE - sortals cannot specialize different kinds
fof(cj_sortalsSpecializeOneKindMax, conjecture, (
    ~?[X,Y,Z]: (kind(Y)&kind(Z)&~(Y=Z)&specializes(X,Y)&specializes(X,Z))    
)).

%%% PROVEN CONJECTURE - a non-sortal cannot specialize a sortal
fof(cj_nonSortalCantSpecializeSortal, conjecture, (
    ~?[X,Y]: (nonsortal(X)&sortal(Y)&specializes(X,Y))
)).

%%% PROVEN CONJECTURE
% Theorem: nonsortals do not have direct instances, their instances are also instances
% of a sortal that either: 
% specializes the nonsortal, or 
% specializes a common nonsortal supertype
fof(cj_nonsortalsNoDirectInstance, conjecture, (
    ![T,X,W]: (
        (nonsortal(T) & iof(X,T,W)) =>
        (
            (?[S]: (sortal(S)&specializes(S,T)&iof(X,S,W))) |
            (?[N,S]: (nonsortal(N)&sortal(S)&specializes(S,N)&specializes(T,N)&iof(X,S,W)))
        )
    )
)).

%%% PROVEN CONJECTURE - Theorem: Leaf categories of UFO taxonomy of types are disjoint
fof(cj_leafNodesTaxonomyTypesDisjoint, conjecture, (
    ![T]: (kind(T) => (~subkind(T) & ~role(T) & ~phase(T) & ~rolemixin(T) & ~phasemixin(T) & ~category(T) & ~mixin(T))) &
    ![T]: (subkind(T) => (~kind(T) & ~role(T) & ~phase(T) & ~rolemixin(T) & ~phasemixin(T) & ~category(T) & ~mixin(T))) &
    ![T]: (role(T) => (~kind(T) & ~subkind(T) & ~phase(T) & ~rolemixin(T) & ~phasemixin(T) & ~category(T) & ~mixin(T))) &
    ![T]: (phase(T) => (~kind(T) & ~subkind(T) & ~role(T) & ~rolemixin(T) & ~phasemixin(T) & ~category(T) & ~mixin(T))) &
    ![T]: (rolemixin(T) => (~kind(T) & ~subkind(T) & ~role(T) & ~phase(T) & ~phasemixin(T) & ~category(T) & ~mixin(T))) &
    ![T]: (phasemixin(T) => (~kind(T) & ~subkind(T) & ~role(T) & ~phase(T) & ~rolemixin(T) & ~category(T) & ~mixin(T))) &
    ![T]: (category(T) => (~kind(T) & ~subkind(T) & ~role(T) & ~phase(T) & ~rolemixin(T) & ~phasemixin(T) & ~mixin(T))) &
    ![T]: (mixin(T) => (~kind(T) & ~subkind(T) & ~role(T) & ~phase(T) & ~rolemixin(T) & ~phasemixin(T) & ~category(T))) 
)).    

%%% PROVEN CONJECTURE - Leaf  Leaf categories of UFO taxonomy of types are complete
fof(cj_leafNodesTaxonomyTypesComplete, conjecture, (
    ![T]: (type_(T)<=>(kind(T)|subkind(T)|role(T)|phase(T)|semirigidsortal(T)|mixin(T)|rolemixin(T)|phasemixin(T)|category(T))) 
)).

%%% PROVEN CONJECTURE - Leaf nodes of the taxonomy of endurants are disjoint and together emcompass all endurants
fof(cj_disjointnessEndurants, conjecture, (
    ![X]: (substantial(X)=>(~relator(X)&~mode(X)&~quality(X))) &
    ![X]: (relator(X)=>(~substantial(X)&~mode(X)&~quality(X))) &
    ![X]: (mode(X)=>(~substantial(X)&~relator(X)&~quality(X))) &
    ![X]: (quality(X)=>(~substantial(X)&~relator(X)&~mode(X))) &
    ![X]: (endurant(X)<=>(substantial(X)|relator(X)|mode(X)|quality(X)))
)).

%%% PROVEN CONJECTURE - Leaf nodes of the taxonomy of endurant types are disjoint 
fof(cj_endurantTypesDisjoint, conjecture, (
    ![X]: (substantialtype(X)=>(~relatortype(X)&~modetype(X)&~qualitytype(X))) &
    ![X]: (relatortype(X)=>(~substantialtype(X)&~modetype(X)&~qualitytype(X))) &
    ![X]: (modetype(X)=>(~substantialtype(X)&~relatortype(X)&~qualitytype(X))) &
    ![X]: (qualitytype(X)=>(~substantialtype(X)&~relatortype(X)&~modetype(X))) 
)).

%%% PROVEN CONJECTURE - Theorem if it is an instance of an endurant kind it must be an endurant
fof(cj_everyEndurant, conjecture, (
    ![X]: ((?[W,K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))& iof(X,K,X)))=>endurant(X))
)).



% %%%%%%%%%%%%%%%%%%%%%% Relations %%%%%%%%%%%%%%%%%%%%%%



% % ![T]: (enduranttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>endurant(X)))))
% fof(relatortype, axiom, (    
%     ~?[X]: (relatortype(X) & enduranttype(X))
% )).

% % TODO define relation type
% % TODO define relation

% %% Substantial types are all those types whose instances are substantials
% %fof(ax_dsubstantialType, axiom, (
% %    ![T]: (substantialtype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>substantial(X)))))
% %)).
% %
% %% Moment types are all those types whose instances are moments
% %fof(ax_dmomentType, axiom, (
% %    ![T]: (momenttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>moment(X)))))
% %)).

% % TODO define inheres in
% % TODO define independent
% % TODO define perdurant

% fof(ax_dexternallydependentmode, axiom, (
%     ![X]: (externallydependentmode(X) <=> 
%         (mode(X) & ?[Y,Z]: (inheresin(X,Z) & externaldependenton(X,Y) & independent(Y,Z)))
%     )
% )).

% fof(ax_foundedby, axiom, (
%     ![X,Y]: (foundedby(X,Y) => (externaldependentmode(X) & perdurant(Y))) 
%     & ![X]: (externallydependentmode(X) => (?[Y]: (foundedby(X,Y)))) 
%     & ![X,Y,Z]: ((foundedby(X,Y) & foundedby(X,Z)) => (Y=Z))
% )).

% fof(ax_dquaindividual, axiom, (
%     ![X]: (quaindividual(X) <=> (?[Y]: quaindividualof(x,y)))
%     & ![X,Y]: (quanindividualof(X,Y) <=> 
%             (?[Z,E]: (externallydepentmode(Z) & perdurant(E) & inheresin(Z,Y) & (X=Z) & foundedby(X,E) & foundedby(Z,E)))
%     ) 
%     & ![X]: (quanindividual(X) => (externallydependentmode(X)))
%     & ![X,Y,Z]: ((quaindividualof(X,Y) & quaindividualof(X,Z)) => (Y=Z))
% )).
% % TODO check this one (a6)... btw, I don't get it
% % The qua individual is a complex mode with a foundation which is the same of some event
% % However, the foundation of the whole is not the same of the parts (not necessarily)
% %D: The new formula should have fixed that  

%  fof(ax_dbinaryrelator, axiom, (
%      ![X]: (relator2(X) => ?[Y]: (foundedby(X,Y)))
%      & ![X]: (relator2(X) <=> 
%          (?[Y,Z,E]: (
%              quaindividual(Y) & quaindividual(Z) & perdurant(E) 
%              & ~(Y=Z) 
%              & foundedby(Y,E) & foundedby(Z,E)
%              & existentiallydependenton(Y,Z) & existentiallydependenton(Z,Y)
%          ))
%      )
%  )).
% % & (X=Y+Z) % it's not possible to say this in this syntax


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Mereology
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_part_rifl, axiom, (![X]: (part(X,X)))).

fof(ax_part_antisymm, axiom, (![X,Y]: ((part(X,Y) & part(Y,X)) => (Y=X)))).

fof(ax_part_trans, axiom, (![X,Y,Z]: ((part(X,Y) & part(Y,Z)) => part(X,Z)))).

fof(ax_part_overlappin, axiom, (![X,Y]: (overlap(X,Y) <=> ?[Z]:(part(Z,X) & part(Z,Y))))).

fof(ax_part_strong_supp, axiom, (![X,Y]: (~part(Y,X) => ?[Z]:(part(Z,Y) & ~overlap(Z,X))))).

fof(ax_part_proper_part, axiom, (![X,Y]: (properPart(Y,X) <=> (part(X,Y) & ~part(Y,X))))).

fof(ax_part_sum, axiom, (![Z,X,Y]: (sum(Z,X,Y) <=> ![W]:((overlap(W,Z) <=> (overlap(W,X) | overlap(W,X))))))).


%from this the unicity of the sum should follow
fof(cj_unicity_sum, conjecture, (?[Z,T,X,Y]: (sum(Z,X,Y) & sum(T,X,Y) & Z!=T))).

%simplified version?
%fof(ax_part_sum, axiom, (![Z,X,Y]: (sum(Z,X,Y) <=> properpart(X,Z) & properpart(Y,Z)))).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Existential dependence
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%everything is a thing, to check if there is something left out...

fof(ax_existence, axiom, (![X]: ((type(X) | individual(X)) => Thing(X))).

%Existence axiom.

fof(ax_existence, axiom, (![X,W]: (ex(X,W) => Thing(X))).

%existential dependence and independence

fof(ax_existential_dependence, axiom, (![X,Y]: (ed(X,Y) <=> ![W](ex(X,W) => ex(Y,W))))).

fof(ax_existential_independence, axiom, (![X,Y]: (ind(X,Y) <=> ~ed(X,Y) & ~ed(Y,X))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Inherence
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Do we need world dependent inherence for the internal properties? inhereIn(X,Y,W)

fof(ax_inherence_type, axiom, (![X,Y]: (inehresIn(X,Y) => moment(X) & endurant(Y)))).


fof(ax_inherence_ed, axiom, (![X,Y]: (inehresIn(X,Y) => ed(X,Y)))).


fof(ax_inherence_irrifl, axiom, (![X]: ~inehresIn(X,X))).


fof(ax_inherence_asymm, axiom, (![X,Y]: ineheresIn(X,Y) => ~inehresIn(Y,X))).


fof(ax_inherence_intrans, axiom, (![X,Y]: (ineheresIn(X,Y) & ineheresIn(Y,Z) => ~inehresIn(X,Z))))).


fof(ax_inherence_unic, axiom, (![X,Y,Z]: (ineheresIn(X,Y) & ineheresIn(X,Z) => Y=Z)))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Intrinsic moments, externally dependent modes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5
					    
fof(ax_moment, axiom, (![X]: (moment(X) <=> endurant(X) & ?[Y]: inheresIn(X,Y)))).
					    
%Externally dependent modes

fof(ax_edm, axiom, (![X]: (edm(X) <=> mode(X) & ?[Y]: (ed(X,Y) & ![Z](inheresIn(X,Z)) => ind(Z,Y))))).
				     
					     
					     
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Properties
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Properites are types

fof(ax_def_propertytype, axiom, (![P] (property(P) => type_(P)))).
fof(ax_def_internalpropertytype, axiom, (![P] (internalproperty(P) => property(P)))).
fof(ax_def_externalpropertytype, axiom, (![P] (externalproperty(P) => property(P)))).
fof(ax_def_intrinsicpropertytype, axiom, (![P] (intrinsicproperty(P) => property(P)))).
fof(ax_def_extrinsicpropertytype, axiom, (![P] (extrinsicproperty(P) => property(P)))).
fof(ax_def_descriptivepropertytype, axiom, (![P] (descriptiveproperty(P) => property(P)))).
fof(ax_def_nondescriptivepropertytype, axiom, (![P] (nondescriptiveproperty(P) => property(P)))).




%Intrinsic property. Simplified without "relevance" relation between a property and internal. For proving is should be sufficient. 
				

fof(ax_def_internalP, axiom, (![P]: (intrinsicproperty(P) <=> ![X](?[W]: (iof(X,P,W) <=> 
	?[M](intrinsicmoment(M) & ineheresIn(M,X))))))).

%Extrinsic
fof(ax_def_externalP, axiom, (![P]: (extrinsicproperty(P) <=>  ~intrinsicproperty(P)))).

%TO CHECK: do we already have intrinsicmoment? yes. 
				
				
%Descriptive and non-descirptive properties.


fof(ax_def_descriptiveP, axiom, (![P]: (descriptiveproperty(P) <=> ![X](?[W](iof(X,P,W) =>
	?[M]: (moment(m) & ineheresIn(M,X))))))).
				
fof(ax_def_nondescriptiveP, axiom, (![P]: (nondescriptiveproperty(P) <=> ~descriptiveproperty(P)))).
								     

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Relations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%<x,y> :: r in world w is defined by iofr(X,Y,R,W)

fof(ax_def_relationstype, axiom, (![R]: (relation(R) => Thing(R)))).
fof(ax_def_relationstype, axiom, (~?[R]: (relation(R) & type_(R)))).
fof(ax_def_relationstype, axiom, (~?[R]: (relation(R) & individual(R)))).


%"instance of" for relation iofr

fof(ax_def_relations, axiom, (![X,Y,R,W] : (iofr(X,Y,R,W) => individual(X) & individual(Y) & relation(R) & world(W)))).

%Internal and external relations are relations

fof(ax_def_relations, axiom, (![R] : ((internalrelation(R) | externalrelation(R)) => relation(R)))).


%Internal and external relations
					     

fof(ax_def_internalrelations, axiom, (![R] : internalrelation(R) <=> ![X,Y]:(?[W]: (iofr(X,Y,R,W) => 
	 ?[P,Q](intrinsicproperty(P) & intrinsicproperty(Q) & iof(X,P,W) & iof(Y,Q,W)))))).
		
					     
fof(ax_def_extenralrelations, axiom, (![R]: (externalrelation(R) <=> ~internalrelation(R)))).
		
%Descriptive and non-descriptive relations

fof(ax_def_descriptiverelations, axiom, (![R] : descriptiverelation(R) <=> ![X,Y]:(?[W]: (iofr(X,Y,R,W) => 
	?[M]: (edm(M) & ((inheresIn(M,X) & ed(M,Y)) | (inheresIn(M,Y) & ed(M,X)))) |
	?[L,N](intrinsicmoment(L) & intrinsicmoment(M) & inheresIn(L,X) & inheresIn(N,Y)))))).
		
		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Sums of Externally dependent modes. Relators.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%Perdurants
fof(ax_def_perdurant, axiom, (![X] : perdurant(X) => thing(X)))).
fof(ax_def_perdurant_disjoint, axiom, (~?[X] : perdurant(X) & endurant(X)))).
fof(ax_def_perdurant_disjoint2, axiom, (~?[X] : perdurant(X) & type_(X)))).

%founded by
 
fof(ax_def_founded_by, axiom, (![X,Y] : (foundedBy(X,Y) => ((edm(X) | relator(X))) & perdurant(Y)))).

%this should simplify a26, 27, and the foundation of relators

fof(ax_def_founded_by_unique, axiom, (![X,Y,Z] : (foundedBy(X,Y) & foundedBy(X,Z) => Y=Z))).

%sumEDM, type

fof(ax_def_founded_sum_edm1, axiom, (![X,Y,Z] : (sumedm(X,Y,E) => individual(Y) & perdurant(E)))). 

%sumEDM, version1	: X is the sum of all the edm that inhere Y and are founded by E.

fof(ax_def_founded_sum_edm1, axiom, (![X,Y,E] : (sumedm(X,Y,E) <=> 
	![V]: (overlap(V,X) <=> ?[W](edm(W) & inheres(W,Y) & foundedBy(W,E) & overlap(W,V)))))). 
	
%Relators

fof(ax_def_relator, axiom, (![X] : (relator(X) <=> ?[Y,Z,V,W,E] (sumedm(Y,V,E) & sumedm(Z,W,E) & properpart(Y,X) &
	 properpart(Z,X) & Y != Z & ed(Y,W) & ed(Z,V))))).
	 
%Involves
fof(ax_def_involves, axiom, (![X,Y] : (involves(X,Y) <=> relator(X) & endurant(Y) & ?[Z,E]:(sumedm(Z,Y,E)) 
	& properpart(Z,X)))).
))).

