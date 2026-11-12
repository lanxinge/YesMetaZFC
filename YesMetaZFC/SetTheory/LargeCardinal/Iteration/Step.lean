import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Limit
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Truncation

/-! # 后继结点的整列嵌入由替代实际收集

旧箭头保持原值；新对角线取恒等图；每条到新结点的祖先箭头是原箭头
与指定后继边的复合。三种情形互斥，复合图唯一，故不需要选择代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_next_d (α k G e t i j f : M.Domain) : Prop := It_map_d G i j f ∨
  j = α ∧ ((i = α ∧ f = e) ∨ ∃ g, It_map_d G i k g ∧ It_comp_d g t f)
def it_next_m {d} (α k G e t i j f : Term d) : Formula 1 d := .disj (it_map_m G i j f)
  (.conj (Formula.extensionalEq j α) (.disj (.conj (Formula.extensionalEq i α) (Formula.extensionalEq f e))
    (.existsE (.conj (it_map_m G.weaken i.weaken k.weaken .newest) (it_comp_m .newest t.weaken f.weaken)))))
derive_free_closed it_next_m

theorem it_next_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (α k G e t i j f : Term d) :
    Formula.satisfies ρ (it_next_m α k G e t i j f) ↔
      It_next_d (α.eval ρ) (k.eval ρ) (G.eval ρ) (e.eval ρ) (t.eval ρ) (i.eval ρ) (j.eval ρ) (f.eval ρ) := by
  simp only [it_next_m, It_next_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_exists_iff,
    it_map_sat_l hKP.1, it_comp_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_next_unique_l {ω α T Q G k e t i j f g : M.Domain} (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G)
    (hf : It_next_d α k G e t i j f) (hg : It_next_d α k G e t i j g) : f = g := by
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  have left {l f} (hf : It_map_d G α l f) : False := no (h.order.bound α l (h.map_bound_l hZF hf)).1
  have right {l f} (hf : It_map_d G l α f) : False := no (h.order.bound l α (h.map_bound_l hZF hf)).2
  rcases hf with hf | ⟨rfl, ⟨rfl, rfl⟩ | ⟨f₀, hf₀, cf⟩⟩
  · rcases hg with hg | ⟨rfl, _⟩
    · exact h.map_unique_l hZF hf hg
    · exact (right hf).elim
  · rcases hg with hg | ⟨_, ⟨_, eq⟩ | ⟨g₀, hg₀, _⟩⟩
    · exact (right hg).elim
    · exact eq.symm
    · exact (left hg₀).elim
  · rcases hg with hg | ⟨_, ⟨rfl, _⟩ | ⟨g₀, hg₀, cg⟩⟩
    · exact (right hg).elim
    · exact (left hf₀).elim
    · exact cf.unique_l hZF.1 ((h.map_unique_l hZF hg₀ hf₀) ▸ cg)

theorem it_next_maps_l {ω α T Q G k c X R d Y e t U : M.Domain}
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (hc : Rd_entry_d k c Q) (mx : Smdl_d I c X R)
    (ht : Smap_d I ω c d X Y t)
    (u : ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T))
    (rel : M.IsSetRelation I U) : ∃ H, M.IsSetFunction I H ∧ M.IsDomainOf I U H ∧
      ∀ i j f, It_map_d H i j f ↔ It_next_d α k G e t i j f := by
  let ρ : Env M 5 := ⟨Fin.cases α (Fin.cases k (Fin.cases G (Fin.cases e (fun _ => t)))), fun _ => α⟩
  let φ : BinarySchema 5 := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 3) (.bound 1) .newest)
      (it_next_m (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest (.bound 2)))) }
  have sat r f : φ.denote ρ r f ↔ ∃ i j, KPair_d M r i j ∧ It_next_d α k G e t i j f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, it_next_sat_l (ZF.modelsKP hZF)]; rfl
  have total r (hr : M.mem r U) : ∃ f, φ.denote ρ r f := by
    obtain ⟨i, j, hp⟩ := rel r hr
    rcases (u i j).mp ⟨r, hp, hr⟩ with hij | ⟨rfl, rfl | hik⟩
    · obtain ⟨f, hf⟩ := h.map_l hZF hij
      exact ⟨f, (sat r f).mpr ⟨i, j, hp, Or.inl hf⟩⟩
    · exact ⟨e, (sat r e).mpr ⟨_, _, hp, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩⟩
    · obtain ⟨f, hf⟩ := h.map_l hZF hik
      obtain ⟨b, Z, V, hb, mb⟩ := h.model_l hZF (h.order.bound i k hik).1
      obtain ⟨g, _, comp⟩ := it_comp_elementary_l hZF (h.elementary i k f b Z V c X R hf hb hc mb mx) ht
      exact ⟨g, (sat r g).mpr ⟨i, _, hp, Or.inr ⟨rfl, Or.inr ⟨f, hf, comp⟩⟩⟩⟩
  have unique r f g (hf : φ.denote ρ r f) (hg : φ.denote ρ r g) : f = g := by
    obtain ⟨i, j, hr, hf⟩ := (sat r f).mp hf
    obtain ⟨i', j', hr', hg⟩ := (sat r g).mp hg
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hr hr'
    exact it_next_unique_l hZF h hf hg
  obtain ⟨B, bs⟩ := ZF.exists_functionalImage hZF φ ρ U total unique
  obtain ⟨H, hh, hs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun r _ => unique r)
    (fun r f hr hf => (bs f).mpr ⟨r, hr, hf⟩)
  refine ⟨H, hh.1, hh.2.1, fun i j f => ⟨?_, ?_⟩⟩
  · rintro ⟨r, hr, hrf⟩
    obtain ⟨i', j', hr', hf⟩ := (sat r f).mp ((hs r f).mp hrf).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hr hr'
    exact hf
  · intro hf
    obtain ⟨r, hr⟩ := (I).total i j
    have hij : Rd_entry_d i j U := by
      apply (u i j).mpr
      rcases hf with hf | ⟨rfl, ⟨rfl, _⟩ | ⟨g, hg, _⟩⟩
      · exact Or.inl (h.map_bound_l hZF hf)
      · exact Or.inr ⟨rfl, Or.inl rfl⟩
      · exact Or.inr ⟨rfl, Or.inr (h.map_bound_l hZF hg)⟩
    obtain ⟨s, hs', hsU⟩ := hij
    have hrU := (kpair_unique_l M hZF.1 hs' hr) ▸ hsU
    exact ⟨r, hr, (hs r f).mpr ⟨hrU, (sat r f).mpr ⟨i, j, hr, hf⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 添枝后完整初等图的交换律

新增模型和全部新增箭头一起构造。旧三角形沿用原交换律；经过新结点的
三角形展开成一次末边复合，逐值计算即得交换，不添加交换律假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_diagram_extend_l {ω α ξ T Q G k c X R d Y S t : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d k c Q) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (ht : Smap_d I ω c d X Y t) :
    ∃ β U Q' G' e, M.SuccessorOf β α ∧ It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' ∧
      (∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T)) ∧
      (∀ i b, Rd_entry_d i b Q' ↔ Rd_entry_d i b Q ∨ i = α ∧ b = d) ∧
      (∀ i j f, It_map_d G' i j f ↔ It_next_d α k G e t i j f) ∧ It_map_d G' k α t := by
  have hk := (h.model_domain k).mpr ⟨c, hc⟩
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  obtain ⟨β, U, hβ, order, us⟩ := it_order_extend_l (ZF.modelsKP hZF) h.order hα hk
  obtain ⟨Q', hQ', qs⟩ := Structure.IsSequenceOfLength.exists_append (value := d) (ZF.modelsKP hZF) I
    ⟨h.order.ordinal, h.model_function, h.model_domain⟩ order.ordinal hβ
  have qold i b (hi : M.mem i α) : Rd_entry_d i b Q' ↔ Rd_entry_d i b Q := (qs i b).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have qtip b : Rd_entry_d α b Q' ↔ b = d := (qs α b).trans
    ⟨fun hh => hh.elim (fun hh => (no ((h.model_domain α).mpr ⟨b, hh⟩)).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := d) (X := Y) hω
  obtain ⟨G', gfun, gdom, gs⟩ := it_next_maps_l hZF h hc mx ht (e := e) us order.relation
  have gold i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have gtip i f : It_map_d G' i α f ↔ (i = α ∧ f = e) ∨ ∃ g, It_map_d G i k g ∧ It_comp_d g t f :=
    (gs i α f).trans ⟨fun hh => hh.elim (fun hh => (no (h.order.bound i α (h.map_bound_l hZF hh)).2).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  have typed i j f b Z V b' Z' V' (hf : It_map_d G' i j f) (hb : Rd_entry_d i b Q') (hb' : Rd_entry_d j b' Q')
      (mb : Smdl_d I b Z V) (mb' : Smdl_d I b' Z' V') : Smap_d I ω b b' Z Z' f := by
    rcases (gs i j f).mp hf with hf | ⟨rfl, ⟨rfl, rfl⟩ | ⟨g, hg, comp⟩⟩
    · have hij := h.order.bound i j (h.map_bound_l hZF hf)
      exact h.elementary i j f b Z V b' Z' V' hf ((qold i b hij.1).mp hb) ((qold j b' hij.2).mp hb') mb mb'
    · have eb := (qtip b).mp hb
      have eb' := (qtip b').mp hb'
      subst b b'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb my
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb' my
      exact he
    · have eb' := (qtip b').mp hb'
      subst b'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb' my
      have gi := h.elementary i k g b Z V c X R hg
        ((qold i b (h.order.bound i k (h.map_bound_l hZF hg)).1).mp hb) hc mb mx
      obtain ⟨f', hf', spec⟩ := it_comp_elementary_l hZF gi ht
      exact spec.unique_l hZF.1 comp ▸ hf'
  have ident i f (hf : It_map_d G' i i f) x y (hxy : Rd_entry_d x y f) : x = y := by
    rcases (gs i i f).mp hf with hf | ⟨rfl, ⟨_, rfl⟩ | ⟨g, hg, _⟩⟩
    · exact h.identity i f hf x y hxy
    · exact ((es x y).mp hxy).2
    · exact (no (h.order.bound _ k (h.map_bound_l hZF hg)).1).elim
  have commute i j l f g v (hf : It_map_d G' i j f) (hg : It_map_d G' j l g) (hv : It_map_d G' i l v)
      x y z (hxy : Rd_entry_d x y f) (hyz : Rd_entry_d y z g) : Rd_entry_d x z v := by
    rcases (gs j l g).mp hg with hg₀ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨g₀, hg₀, cg⟩⟩
    · obtain ⟨hj, hl⟩ := h.order.bound j l (h.map_bound_l hZF hg₀)
      exact h.comp i j l f g v ((gold i j f hj).mp hf) hg₀ ((gold i l v hl).mp hv) x y z hxy hyz
    · have eq := it_next_unique_l hZF h ((gs i _ f).mp hf) ((gs i _ v).mp hv)
      exact eq ▸ ((es y z).mp hyz).2 ▸ hxy
    · have hf₀ := (gold i j f (h.order.bound j k (h.map_bound_l hZF hg₀)).1).mp hf
      rcases (gtip i v).mp hv with ⟨rfl, _⟩ | ⟨v₀, hv₀, cv⟩
      · exact (no (h.order.bound _ j (h.map_bound_l hZF hf₀)).1).elim
      · obtain ⟨w, hyw, hwz⟩ := (cg.2 y z).mp hyz
        exact (cv.2 x z).mpr ⟨w, h.comp i j k f g₀ v₀ hf₀ hg₀ hv₀ x y w hxy hyw, hwz⟩
  have diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' := ⟨order, hQ'.2.1, hQ'.2.2, fun i b hb => by
      rcases (qs i b).mp hb with hb | ⟨rfl, rfl⟩
      · exact h.models i b hb
      · exact ⟨Y, S, my⟩,
    gfun, gdom, typed, ident, commute⟩
  obtain ⟨f, hf⟩ := h.map_l hZF (h.order.refl k hk)
  have ff := h.elementary k k f c X R c X R hf hc hc mx mx
  have idcomp : It_comp_d f t t := ⟨ht.1.1.1.1, fun x y => ⟨fun hxy => by
    obtain ⟨z, _, hxz⟩ := ff.1.1.2.2 x (ht.1.1.input_mem_of_pairMember hxy)
    exact ⟨x, (h.identity k f hf x z hxz).symm ▸ hxz, hxy⟩,
    fun ⟨z, hxz, hzy⟩ => (h.identity k f hf x z hxz).symm ▸ hzy⟩⟩
  exact ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs,
    (gtip k t).mpr (Or.inr ⟨f, hf, idcomp⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 一条实际超幂边及其所属模型

边证书同时保留源内部代表、商、常值图和坍塌；新边就是这些实际图的
复合。所属模型对扩展器的判断使用原短扩展器公式的相对满足关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 节点保存原关系源及完整数字坐标；自然数对象不必是背景 ω。 -/
structure It_source_d (hZF : M.Models ZF) (ω c : M.Domain) : Prop where
  omega : M.IsOmega ω
  objects : ∃ X R w K z, Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R ∧
    Er_source_d (kp_pair_l (ZF.modelsKP hZF)) ω w w K X R ∧
    Rr_layer_d (kp_pair_l (ZF.modelsKP hZF)) ω X R w z

/-- 完整源及数字坐标一起回拉，不要求初等子模型的载体传递。 -/
theorem It_source_d.pull_l (hZF : M.Models ZF) {Ω c X R d Y S q : M.Domain}
    (h : It_source_d hZF Ω d) (mx : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (my : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (map : Smap_d (kp_pair_l (ZF.modelsKP hZF)) Ω c d X Y q) : It_source_d hZF Ω c := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Y₀, S₀, v, K, t, code, core, numbers⟩ := h.objects
  obtain ⟨eqY, eqS⟩ := smdl_unique_l I code my
  subst Y₀ S₀
  let A := smdl_structure_l I (R := R) mx.2.1
  let B := smdl_structure_l I (R := S) my.2.1
  have ey := core.ext.native_l I my.2.1
  have nv : B.IsOmega ⟨v, numbers.member⟩ := numbers.omega_l I (ZF.modelsKP hZF) h.omega ey
  obtain ⟨a, ha⟩ := mx.2.1
  let ρ : Env A 0 := ⟨Fin.elim0, fun _ => ⟨a, ha⟩⟩
  let η : Env B 0 := ⟨Fin.elim0, fun _ => ⟨v, numbers.member⟩⟩
  let φ : Formula 1 0 := .existsE (Formula.isOmega .newest)
  have tr := smap_source_l I hZF h.omega mx my map φ
    (by simp -implicitDefEqProofs [φ, Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed])
    ρ η (fun i => Fin.elim0 i)
  have existsω : ∃ w : A.Domain, A.IsOmega w := by
    obtain ⟨w, nw⟩ := tr.mpr (show Formula.satisfies η φ from
      ⟨⟨v, numbers.member⟩, (Formula.satisfies_isOmega_iff ..).mpr nv⟩)
    exact ⟨w, (Formula.satisfies_isOmega_iff (ρ.push w) .newest).mp nw⟩
  obtain ⟨w, nw⟩ := existsω
  obtain ⟨v', hv', image⟩ := map.1.1.2.2 w.val w.property
  let ρ₁ : Env A 1 := ⟨fun _ => w, fun _ => w⟩
  let η₁ : Env B 1 := ⟨fun _ => ⟨v', hv'⟩, fun _ => ⟨v', hv'⟩⟩
  have nv' : B.IsOmega ⟨v', hv'⟩ := (Formula.satisfies_isOmega_iff η₁ .newest).mp
    ((smap_source_l I hZF h.omega mx my map (Formula.isOmega .newest)
      (by simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed])
      ρ₁ η₁ (fun _ => image)).mp ((Formula.satisfies_isOmega_iff ρ₁ .newest).mpr nw))
  have eq : v' = v := congrArg Subtype.val (ey.eq_of_same_members ⟨v', hv'⟩ ⟨v, numbers.member⟩
    (fun x => ⟨nv'.2 _ nv.1 x, nv.2 _ nv'.1 x⟩))
  subst v'
  obtain ⟨L, source⟩ := core.pull_l I hZF h.omega mx my map image image
  obtain ⟨z, layer, _⟩ := numbers.omega_pull_l I hZF h.omega mx my map image core.ext
  exact ⟨h.omega, X, R, w.val, L, z, mx, source, layer⟩

/-- 实际传递隶属呈示只供需要背景成员关系的读取使用。 -/
def It_mem_d (I : kpair_convention_l.Interpretation M) (c : M.Domain) : Prop :=
  ∃ X R, Smem_d I c X R ∧ M.TransitiveSet X

/-- 现有隶属源给出同一个原关系节点，数字图由恒等限制实际构造。 -/
theorem it_source_mem_l (hZF : M.Models ZF) {ω c X R K : M.Domain}
    (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K X R) : It_source_d hZF ω c := by
  obtain ⟨z, numbers, _⟩ := rr_layer_mem_l (kp_pair_l (ZF.modelsKP hZF)) hZF model source.transitive
    source.omega_mem (source.omega.transitive (ZF.modelsKP hZF))
  exact ⟨source.omega, X, R, ω, K, z, model.1, source.toEr_source_d, numbers⟩

/-- 原关系源的字面读取必须使用这个节点的实际传递隶属证据。 -/
theorem It_source_d.mem_l (hZF : M.Models ZF) {ω c : M.Domain} (h : It_source_d hZF ω c)
    (mem : It_mem_d (kp_pair_l (ZF.modelsKP hZF)) c) :
    ∃ X R K, Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R ∧
      Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K X R := by
  obtain ⟨X, R, w, K, z, model, source, numbers⟩ := h.objects
  obtain ⟨Y, S, literal, trans⟩ := mem
  obtain ⟨eqX, eqR⟩ := smdl_unique_l (kp_pair_l (ZF.modelsKP hZF)) literal.1 model
  subst Y S
  obtain ⟨eq, _⟩ := numbers.omega_mem_l (kp_pair_l (ZF.modelsKP hZF)) (ZF.modelsKP hZF) h.omega trans literal
  subst w
  exact ⟨X, R, K, literal, source, h.omega, fun _ hx => hx, trans, numbers.member, numbers.member, c, literal⟩

/-- 原生源的实际传递隶属像自动成为完整隶属源；不要求原载体已坍塌。 -/
theorem It_source_d.image_mem_l (hZF : M.Models ZF) {Ω c X R d Y S q : M.Domain}
    (h : It_source_d hZF Ω c) (mx : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (my : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S) (trans : M.TransitiveSet Y)
    (map : Smap_d (kp_pair_l (ZF.modelsKP hZF)) Ω c d X Y q) :
    ∃ L, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) Ω Ω L Y S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨X₀, R₀, w, K, z, code, core, numbers⟩ := h.objects
  obtain ⟨eqX, eqR⟩ := smdl_unique_l I code mx
  subst X₀ R₀
  have image := (numbers.omega_image_mem_l I hZF h.omega core.ext mx my trans map).1
  have hv := map.1.1.output_mem_of_pairMember image
  have seq := (sc_sequences_iff_l I hZF h.omega mx my.1 map image).mp core.sequences
  obtain ⟨L, finite⟩ := seq.space_l I hv
  have ext := rf_ext_mem_l I hZF.1 trans my
  have source := Er_source_d.of_mem_l I hZF.1 h.omega trans my hv
    ((map.small_l I hZF h.omega mx my.1 image).mp core.cardinal_small) finite
    (core.theory.map_l I hZF h.omega mx my.1 map)
    (core.collection.map_l I hZF h.omega mx my.1 (core.ext.native_l I mx.2.1) (ext.native_l I my.1.2.1) map)
    seq ((sc_collapse_iff_l I hZF h.omega mx my.1 map).mp core.collapse)
  exact ⟨L, source, h.omega, fun _ hx => hx, trans, hv, hv, d, my⟩

/-- 所属判断直接解释原关系；这里既不要求传递载体，也不要求超幂良基。 -/
def It_local_d (I : kpair_convention_l.Interpretation M) (ω X R κ L F : M.Domain) : Prop :=
  ∃ hω : M.mem ω X, ∃ hκ : M.mem κ X, ∃ hL : M.mem L X, ∃ hF : M.mem F X,
    Formula.satisfies (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩))),
      fun _ => ⟨ω, hω⟩⟩ : Env (smdl_structure_l I (R := R) ⟨ω, hω⟩) 4)
      (ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0))

/-- 只有实际隶属关系码才能把所属判断读成普通子模型中的原公式。 -/
theorem it_local_mem_l (I : kpair_convention_l.Interpretation M) {ω X R κ L F : M.Domain}
    (code : ∃ c, Smem_d I c X R) : It_local_d I ω X R κ L F ↔
      ∃ hω : M.mem ω X, ∃ hκ : M.mem κ X, ∃ hL : M.mem L X, ∃ hF : M.mem F X,
        Formula.satisfies (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩))),
          fun _ => ⟨ω, hω⟩⟩ : Env (rt_model_l X ⟨⟨ω, hω⟩⟩) 4)
          (ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)) := by
  obtain ⟨c, model⟩ := code
  exact exists_congr fun hw => exists_congr fun hk => exists_congr fun hl => exists_congr fun hf =>
    (smem_formula_l I model ⟨⟨ω, hw⟩⟩ _
      ⟨Fin.cases ⟨F, hf⟩ (Fin.cases ⟨L, hl⟩ (Fin.cases ⟨κ, hk⟩ (fun _ => ⟨ω, hw⟩))),
        fun _ => ⟨ω, hw⟩⟩).symm

def It_ultra_d (I : kpair_convention_l.Interpretation M) (ω κ L F c d j : M.Domain) : Prop :=
  ∃ X R Y S J O Z A p T V q b C W i e,
    Smem_d I c X R ∧ Smem_d I d Y S ∧
    Ep_system_d I ω κ L X R F J O Z A p T V ∧ Di_limit_d A p T V q C W ∧ Smdl_d I b C W ∧
    Wc_graph_d C W e ∧ M.IsSetBijectionFromTo I e C Y ∧ Smap_d I ω b d C Y e ∧
    Smap_d I ω c b X C i ∧ Ep_constants_d X q i ∧ Smap_d I ω c d X Y j ∧ It_comp_d i e j

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际超幂的塌缩证书保证目标传递，无需另加目标源证书。 -/
theorem It_ultra_d.transitive_l {ω κ L F c d j Y S : M.Domain} (h : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j)
    (hn : Smdl_d I d Y S) : M.TransitiveSet Y := by
  obtain ⟨_, _, Y', S', _, _, _, _, _, _, _, _, _, _, _, _, _, _, my, _, _, _, wc, bij, _⟩ := h
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 hn
  intro x hx y hy
  obtain ⟨E, _, hEx⟩ := bij.2 x hx
  obtain ⟨H, _, _, hHy⟩ := ((wc.2 E x hEx).2.2 y).mp hy
  exact bij.1.1.output_mem_of_pairMember hHy

/-- 真实坍塌产生实际呈示；这一证据不放入一般原关系节点条件。 -/
theorem It_ultra_d.target_mem_l {ω κ L F c d j : M.Domain}
    (h : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j) : It_mem_d I d := by
  have data := h
  obtain ⟨_, _, Y, S, _, _, _, _, _, _, _, _, _, _, _, _, _, _, model, _⟩ := data
  exact ⟨Y, S, model, h.transitive_l hZF model.1⟩

theorem It_ultra_d.elementary_l {ω κ L F c d j X R Y S : M.Domain} (h : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j)
    (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S) : Smap_d I ω c d X Y j := by
  obtain ⟨X', R', Y', S', _, _, _, _, _, _, _, _, _, _, _, _, _, mx, my, _, _, _, _, _, _, _, _, hj, _⟩ := h
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx.1 hm
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 hn
  exact hj

/-- 已构造的良基超幂自动给出新模型码、实际超幂边及下一步源。 -/
theorem it_ultra_exists_l {ω κ L X R F c : M.Domain}
    (code : Smem_d I c X R)
    (built : Ep_limit_d hZF ω κ L X R F) : ∃ d j, It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j ∧ It_source_d hZF ω d := by
  obtain ⟨J, O, Z, A, p, T, V, q, b, C, W, hs, limit, model, _, _, collapse⟩ := built
  obtain ⟨_, c', i, Y, e, _, d, S, j, code', hi, constants, hY, wc, bij, target, he, _, _, _, hj, js, next⟩ := collapse
  obtain ⟨rfl, _⟩ := smem_unique_l I hZF.1 code' code
  obtain ⟨K', source'⟩ := next
  exact ⟨d, j, ⟨X, R, Y, S, J, O, Z, A, p, T, V, q, b, C, W, i, e, code, target, hs, limit, model,
      wc, bij, he, hi, constants, hj, hj.1.1.1.1, fun x y => (js x y).trans
        ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩,
    it_source_mem_l hZF target source'⟩

/-- 模型内实际短扩展器直接给出原关系所属证书。 -/
theorem it_local_short_l (J : kpair_convention_l.Interpretation M) {X R : M.Domain}
    (hn : ∃ x, M.mem x X) (K : kpair_convention_l.Interpretation (smdl_structure_l J (R := R) hn))
    (ext : Extensional (smdl_structure_l J (R := R) hn))
    {ω κ L F : (smdl_structure_l J (R := R) hn).Domain}
    (h : Ex_short_d K ω κ L F) : It_local_d J ω.val X R κ.val L.val F.val := by
  let ρ : Env (smdl_structure_l J (R := R) hn) 4 :=
    ⟨Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => ω))), fun _ => ω⟩
  exact ⟨ω.property, κ.property, L.property, F.property,
    (ex_short_sat_l K ext ρ (.bound 3) (.bound 2) (.bound 1) (.bound 0)).mpr h⟩

/-- 读取同一所属公式只需配对解释和外延性，不需所属结构满足 ZF。 -/
theorem It_local_d.read_l (J : kpair_convention_l.Interpretation M) {X R : M.Domain}
    (nx : ∃ x, M.mem x X) (K : kpair_convention_l.Interpretation (smdl_structure_l J (R := R) nx))
    (ext : Extensional (smdl_structure_l J (R := R) nx))
    (ω κ L F : (smdl_structure_l J (R := R) nx).Domain)
    (h : It_local_d J ω.val X R κ.val L.val F.val) : Ex_short_d K ω κ L F := by
  obtain ⟨_, _, _, _, valid⟩ := h
  let ρ : Env (smdl_structure_l J (R := R) nx) 4 :=
    ⟨Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => ω))), fun _ => ω⟩
  exact (ex_short_sat_l K ext ρ (.bound 3) (.bound 2) (.bound 1) .newest).mp valid

/-- 全初等图搬运原关系所属；内部 ω 也由同一实际图搬运。 -/
theorem It_local_d.map_l {Ω ω ω' X R Y S c d σ κ κ' L L' F F' : M.Domain}
    (hΩ : M.IsOmega Ω) (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S)
    (hσ : Smap_d I Ω c d X Y σ) (hω : Rd_entry_d ω ω' σ)
    (hκ : Rd_entry_d κ κ' σ) (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (loc : It_local_d I ω X R κ L F) : It_local_d I ω' Y S κ' L' F' := by
  obtain ⟨ωX, κX, LX, FX, hs⟩ := loc
  have owned {a b} (h : Rd_entry_d a b σ) := hσ.1.1.output_mem_of_pairMember h
  let ρ : Env (smdl_structure_l I (R := R) ⟨ω, ωX⟩) 4 :=
    ⟨Fin.cases ⟨F, FX⟩ (Fin.cases ⟨L, LX⟩ (Fin.cases ⟨κ, κX⟩ (fun _ => ⟨ω, ωX⟩))), fun _ => ⟨ω, ωX⟩⟩
  let η : Env (smdl_structure_l I (R := S) ⟨ω', owned hω⟩) 4 :=
    ⟨Fin.cases ⟨F', owned hF⟩ (Fin.cases ⟨L', owned hL⟩ (Fin.cases ⟨κ', owned hκ⟩
      (fun _ => ⟨ω', owned hω⟩))), fun _ => ⟨ω', owned hω⟩⟩
  exact ⟨owned hω, owned hκ, owned hL, owned hF,
    (smap_source_l I hZF hΩ hm hn hσ _ (ex_short_m_freeClosed _ _ _ _ rfl rfl rfl rfl)
      ρ η (Fin.cases hF (Fin.cases hL (Fin.cases hκ (fun _ => hω))))).mp hs⟩

end YesMetaZFC.SetTheory.LargeCardinal
