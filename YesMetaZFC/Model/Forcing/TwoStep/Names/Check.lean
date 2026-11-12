import YesMetaZFC.Model.Forcing.TwoStep.Names.Valuation
import YesMetaZFC.Model.Forcing.Names.SequenceForcing
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # 二步展开保持规范名称

在地模型的传递容器上收集 y ↦ Curry(check(y))，再将这张实际集合图求值。
其值满足第二阶段 check 递归，因此无需对外部商值作成员归纳。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (generic : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O generic

/-- 首次求值将二步 check 名称变成第二阶段的实际 check 名称。 -/
theorem curry_check_l (h : Two_step_d M B R z b A T W C S)
    {c p s x t v} (hc : M.mem c C) (pair : KPair_d M c p s) (hp : U p)
    (check : Check_d M c x t) (curry : Curry_d M B C t v)
    {q a : (E).Domain} (sq : Qval_d M B R z U s q) (va : Qval_d M B R z U v a)
    (j : M.Domain → (E).Domain) (inj : Function.Injective j)
    (full : ∀ x y, (E).mem y (j x) ↔ ∃ z, M.mem z x ∧ j z = y)
    (checks : ∀ x t, Check_d M p x t → Qval_d M B R z U t (j x)) :
    Check_d E q (j x) a := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X,hX⟩ := ZF.tc_exists_l I hZF x
  let ρ : Env M 3 := ⟨fun i => [B,C,c].get i,fun _ => B⟩
  let φ : BinarySchema 3 := {
    body := .existsE (.conj (check_m (.bound 5) (.bound 2) .newest)
      (curry_m (.bound 3) (.bound 4) .newest (.bound 1))) }
  have sat y v : φ.denote ρ y v ↔ ∃ t, Check_d M c y t ∧ Curry_d M B C t v := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      check_sat_l M hZF.1,curry_sat_l M hZF.1]
    rfl
  have total y (_ : M.mem y X) : ∃ v, φ.denote ρ y v := by
    obtain ⟨t,ht,_,_⟩ := zf_check_l M hZF hc y
    obtain ⟨v,hv⟩ := curry_exists_l M hZF B C t
    exact ⟨v,(sat y v).mpr ⟨t,ht,hv⟩⟩
  have unique y (_ : M.mem y X) v w (hv : φ.denote ρ y v) (hw : φ.denote ρ y w) : v = w := by
    obtain ⟨t,ht,hv⟩ := (sat y v).mp hv
    obtain ⟨s,hs,hw⟩ := (sat y w).mp hw
    have eq := check_unique_l M hZF.1 (check_ind_l M hZF) c y t s ht hs
    subst s
    exact curry_unique_l M hZF.1 (check_ind_l M hZF) B C t v w hv hw
  obtain ⟨Y,range⟩ := ZF.exists_functionalImageOn hZF φ ρ X total unique
  obtain ⟨F,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun y v hy hv => (range v).mpr ⟨y,hy,hv⟩)
  have names y v (yv : Entry_d M y v F) : Name_d M B v := by
    obtain ⟨t,_,hv⟩ := (sat y v).mp ((graph y v).mp yv).2
    obtain ⟨w,hw,hn,_⟩ := two_step_curry_l M hZF h t
    exact curry_unique_l M hZF.1 (check_ind_l M hZF) B C t w v hw hv ▸ hn
  obtain ⟨n,hn⟩ := nseq_exists_l M hZF (generic.proper p hp).1 fn names
  obtain ⟨G,nG⟩ := name_value_l (R := R) (z := z) (U := U) hn.1
  obtain ⟨rel,entries⟩ := nseq_value_l O hZF generic (generic.proper p hp).1 hn nG j checks
  have edges y a : Entry_d E y a G ↔
      ∃ k t v, M.mem k X ∧ Check_d M c k t ∧ Curry_d M B C t v ∧ j k = y ∧ Qval_d M B R z U v a := by
    apply (entries y a).trans
    constructor
    · rintro ⟨k,v,kv,eq,va⟩
      obtain ⟨hk,kv⟩ := (graph k v).mp kv
      obtain ⟨t,kt,tv⟩ := (sat k v).mp kv
      exact ⟨k,t,v,hk,kt,tv,eq,va⟩
    · rintro ⟨k,t,v,hk,kt,tv,eq,va⟩
      exact ⟨k,v,(graph k v).mpr ⟨hk,(sat k v).mpr ⟨t,kt,tv⟩⟩,eq,va⟩
  refine ⟨G,⟨rel,?_⟩,(edges (j x) a).mpr ⟨x,t,v,hX.2.1,check,curry,rfl,va⟩⟩
  intro y a ya
  obtain ⟨k,t,v,hk,kt,tv,rfl,va⟩ := (edges y a).mp ya
  constructor
  · intro y hy
    obtain ⟨l,lk,rfl⟩ := (full k y).mp hy
    obtain ⟨t',lt⟩ := check_child_l M kt lk
    obtain ⟨v',tv',nv',_⟩ := two_step_curry_l M hZF h t'
    obtain ⟨a',va'⟩ := name_value_l (R := R) (z := z) (U := U) nv'
    exact ⟨a',(edges (j l) a').mpr ⟨l,t',v',hX.1 k hk l lk,lt,tv',rfl,va'⟩⟩
  · intro r
    constructor
    · intro ra
      obtain ⟨t',c',v',p',s',a',q',tc,hc',pair',hp',tv',va',sq',rp⟩ :=
        (curry_val_mem_l O hZF generic h tv va).mp ra
      obtain ⟨eq,l,lk,lt⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) kt t' c').mp tc
      subst c'
      obtain ⟨ep,es⟩ := kpair_injective_l M pair' pair
      subst p' s'
      have eq := qval_unique_l sq' sq
      exact ⟨j l,a',(full k (j l)).mpr ⟨l,lk,rfl⟩,
        (edges (j l) a').mpr ⟨l,t',v',hX.1 k hk l lk,lt,tv',rfl,va'⟩,eq ▸ rp⟩
    · rintro ⟨y,a',hy,ya',rp⟩
      obtain ⟨l,lk,eq⟩ := (full k y).mp hy
      obtain ⟨l',t',v',_,lt,tv',eq',va'⟩ := (edges y a').mp ya'
      have same := inj (eq'.trans eq.symm)
      subst l'
      exact (curry_val_mem_l O hZF generic h tv va).mpr ⟨t',c,v',p,s,a',q,
        (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) kt t' c).mpr
          ⟨rfl,l,lk,lt⟩,hc,pair,hp,tv',va',sq,rp⟩

/-- 二步求值同构与任一实际规范嵌入交换；参数沿原求值方程自动保留。 -/
theorem curry_ground_l (h : Two_step_d M B R z b A T W C S)
    {Q D : (E).Domain} {H : (E).Domain → Prop}
    (K : Cond_order_d E Q D Q) (second : Generic_d E Q D Q H)
    (source : Generic_d M C S C (Compose_generic_d M B R z C U H))
    (f : (extension_l M hZF C S C (Compose_generic_d M B R z C U H)).Domain →
      (extension_l E (preserves_zf_l O hZF generic) Q D Q H).Domain)
    (values : ∀ a t, Qval_d M C S C (Compose_generic_d M B R z C U H) t a →
      Curry_val_d M hZF B R z C U Q D H t (f a))
    (inj : Function.Injective f) {r} (hr : U r)
    (j : M.Domain → (E).Domain)
    (checks : ∀ x t, Check_d M r x t → Qval_d M B R z U t (j x)) :
    ∀ x a, Gval_d M C S C (Compose_generic_d M B R z C U H) x a ↔
      Gval_d E Q D Q H (j x) (f a) := by
  have over x a (ha : Gval_d M C S C (Compose_generic_d M B R z C U H) x a) :
      Gval_d E Q D Q H (j x) (f a) := by
    obtain ⟨c,t,⟨hc,p,s,q,cp,hp,sq,hq⟩,ht,ta⟩ := ha
    obtain ⟨v,y,tv,vy,yf⟩ := values a t ta
    obtain ⟨i,ic,full,ii⟩ := check_map_l O hZF generic hp
    have check := curry_check_l O hZF generic h hc cp hp ht tv sq vy i ii full ic
    obtain ⟨s',xs,_,_⟩ := zf_check_l M hZF (generic.proper p hp).1 x
    have eq := (gval_check_map_l O hZF generic hr j checks x (i x)).mp
      ⟨p,s',hp,xs,ic x s' xs⟩
    exact ⟨q,y,hq,eq.symm ▸ check,yf⟩
  intro x a
  refine ⟨over x a,fun ha => ?_⟩
  obtain ⟨d,hd⟩ := gval_exists_l hZF source x
  exact inj ((over x d hd).unique_l K (preserves_zf_l O hZF generic) second ha) ▸ hd

end YesMetaZFC.Model.Forcing.Internal
