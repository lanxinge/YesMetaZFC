import YesMetaZFC.Model.Forcing.Iteration.Names.Generic
import YesMetaZFC.Model.Forcing.Extension.Choice

/-! # 泛型条件中指定坐标的并图

先在扩张内取得实际泛型集合，再用替换取指定坐标，最后取并。
共同加强保证并图单值；每条边都保留原泛型条件及其坐标行的来源。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem generic_coordinate_l {B R z i X Y b : M.Domain} (O : Cond_order_d M B R z)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hb : G b)
    (blocks : ∀ p, G p → M.IsSetFunction I p)
    (rows : ∀ p, G p → ∃ s, Entry_d M i s p)
    (pfn : ∀ p, G p → ∀ s, Entry_d M i s p → Pfn_d I X Y s)
    (mono : ∀ p q, Entry_d M p q R → ∀ s t,
      Entry_d M i s p → Entry_d M i t q → M.MemberSubset t s)
    (input : ∀ a, M.mem a X → ∃ p, G p ∧ ∃ s c, Entry_d M i s p ∧ Entry_d M a c s)
    (e : M.Domain → (extension_l M hZF B R z G).Domain) (inj : Function.Injective e)
    (full : ∀ a y, (extension_l M hZF B R z G).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z G t (e a)) :
    let E := extension_l M hZF B R z G
    let J := kpair_interpretation_l E (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)
    ∃ f, E.IsSetFunctionFromTo J f (e X) (e Y) ∧
      ∀ x y, Entry_d E x y f ↔ ∃ p, G p ∧ ∃ s a c,
        Entry_d M i s p ∧ Entry_d M a c s ∧ e a = x ∧ e c = y := by
  let E := extension_l M hZF B R z G
  have hE := preserves_zf_l O hZF generic
  obtain ⟨γ,name⟩ := gname_exists_l hZF (generic.proper b hb).1
  obtain ⟨U,value⟩ := name_value_l (R := R) (z := z) (U := G) name.1
  have accepted := gname_value_l hZF O generic name value e checks
  have row p (hp : G p) y : Entry_d E (e i) y (e p) ↔ ∃ s, Entry_d M i s p ∧ e s = y := by
    apply (image_entries_l e full (blocks p hp).1 (e i) y).trans
    exact ⟨fun ⟨a,s,edge,eq,ey⟩ => ⟨s,inj eq ▸ edge,ey⟩,
      fun ⟨s,edge,eq⟩ => ⟨i,s,edge,rfl,eq⟩⟩
  let ρ : Env E 1 := ⟨fun _ => e i,fun _ => e i⟩
  let φ : BinarySchema 1 := { body := entry_m (.bound 2) .newest (.bound 1) }
  have sat p s : φ.denote ρ p s ↔ Entry_d E (e i) s p := entry_sat_l E hE.1 ..
  obtain ⟨V,members⟩ := ZF.exists_functionalImageOn hE φ ρ U (fun p hp => by
    obtain ⟨q,hq,rfl⟩ := (accepted p).mp hp
    obtain ⟨s,edge⟩ := rows q hq
    exact ⟨e s,(sat (e q) (e s)).mpr ((row q hq (e s)).mpr ⟨s,edge,rfl⟩)⟩) (by
    intro p hp s t hs ht
    obtain ⟨q,hq,rfl⟩ := (accepted p).mp hp
    obtain ⟨a,ia,rfl⟩ := (row q hq s).mp ((sat (e q) s).mp hs)
    obtain ⟨c,ic,rfl⟩ := (row q hq t).mp ((sat (e q) t).mp ht)
    exact congrArg e ((blocks q hq).2 i a c ia ic))
  obtain ⟨f,union⟩ := KP.exists_union (ZF.modelsKP hE) V
  have mem x : E.mem x f ↔ ∃ p, G p ∧ ∃ s a, Entry_d M i s p ∧ M.mem a s ∧ e a = x := by
    constructor
    · intro hx
      obtain ⟨s,hs,hxs⟩ := (union x).mp hx
      obtain ⟨p,hp,ps⟩ := (members s).mp hs
      obtain ⟨q,hq,rfl⟩ := (accepted p).mp hp
      obtain ⟨t,it,rfl⟩ := (row q hq s).mp ((sat (e q) s).mp ps)
      obtain ⟨a,ha,eq⟩ := (full t x).mp hxs
      exact ⟨q,hq,t,a,it,ha,eq⟩
    · rintro ⟨p,hp,s,a,is,ha,rfl⟩
      exact (union (e a)).mpr ⟨e s,(members (e s)).mpr ⟨e p,
        (accepted (e p)).mpr ⟨p,hp,rfl⟩,(sat (e p) (e s)).mpr ((row p hp (e s)).mpr ⟨s,is,rfl⟩)⟩,
        (full s (e a)).mpr ⟨a,ha,rfl⟩⟩
  have graph x y : Entry_d E x y f ↔ ∃ p, G p ∧ ∃ s a c,
      Entry_d M i s p ∧ Entry_d M a c s ∧ e a = x ∧ e c = y := by
    constructor
    · rintro ⟨v,pair,hv⟩
      obtain ⟨p,hp,s,v,is,vs,rfl⟩ := (mem v).mp hv
      obtain ⟨a,c,ac⟩ := (pfn p hp s is).1.1 v vs
      obtain ⟨eq₀,eq₁⟩ := kpair_injective_l E (image_kpair_l e full ac) pair
      exact ⟨p,hp,s,a,c,is,⟨v,ac,vs⟩,eq₀,eq₁⟩
    · rintro ⟨p,hp,s,a,c,is,⟨v,ac,hv⟩,rfl,rfl⟩
      exact ⟨e v,image_kpair_l e full ac,(mem (e v)).mpr ⟨p,hp,s,v,is,hv,rfl⟩⟩
  refine ⟨f,⟨⟨?_,?_⟩,?_,?_⟩,graph⟩
  · intro v hv
    obtain ⟨p,hp,s,a,is,ha,rfl⟩ := (mem v).mp hv
    obtain ⟨x,y,xy⟩ := (pfn p hp s is).1.1 a ha
    exact ⟨e x,e y,image_kpair_l e full xy⟩
  · intro x y z xy xz
    obtain ⟨p,hp,s,a,c,is,ac,ax,cy⟩ := (graph x y).mp xy
    obtain ⟨q,hq,t,d,v,it,dv,dx,vz⟩ := (graph x z).mp xz
    have eq := inj (ax.trans dx.symm)
    subst d
    obtain ⟨r,hr,rp,rq⟩ := generic.directed p q hp hq
    obtain ⟨w,iw⟩ := rows r hr
    have lift {s a c} (sub : M.MemberSubset s w) (edge : Entry_d M a c s) : Entry_d M a c w :=
      edge.elim fun v h => ⟨v,h.1,sub v h.2⟩
    have eq := (pfn r hr w iw).1.2 a c v (lift (mono r p rp w s iw is) ac) (lift (mono r q rq w t iw it) dv)
    exact cy.symm.trans ((congrArg e eq).trans vz)
  · intro x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := (full X x).mp hx
      obtain ⟨p,hp,s,c,is,ac⟩ := input a ha
      exact ⟨e c,(graph (e a) (e c)).mpr ⟨p,hp,s,a,c,is,ac,rfl,rfl⟩⟩
    · rintro ⟨y,xy⟩
      obtain ⟨p,hp,s,a,c,is,ac,rfl,_⟩ := (graph x y).mp xy
      exact (image_member_l e inj full).mpr ((pfn p hp s is).2 a c ac).1
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (full X x).mp hx
    obtain ⟨p,hp,s,c,is,ac⟩ := input a ha
    exact ⟨e c,(image_member_l e inj full).mpr ((pfn p hp s is).2 a c ac).2,
      (graph (e a) (e c)).mpr ⟨p,hp,s,a,c,is,ac,rfl,rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal
