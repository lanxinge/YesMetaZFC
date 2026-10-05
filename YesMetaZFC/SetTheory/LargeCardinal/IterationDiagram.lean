import YesMetaZFC.SetTheory.LargeCardinal.IterationOrder
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingComposition

/-! # 迭代树上的实际模型图与嵌入图

Q 按结点存结构码，G 按有序对 (i,j) 存完整初等嵌入。全部数据均是
对象模型中的集合；函数性、恒等与复合律允许沿任意树枝读取同一张图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_map_d (G i j f : M.Domain) : Prop := ∃ r, KPair_d M r i j ∧ Rd_entry_d r f G
def it_map_m {d} (G i j f : Term d) : Formula 1 d := .existsE
  (.conj (kpair_m .newest i.weaken j.weaken) (rd_entry_m .newest f.weaken G.weaken))
derive_free_closed it_map_m

theorem it_map_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G i j f : Term d) :
    Formula.satisfies ρ (it_map_m G i j f) ↔ It_map_d (G.eval ρ) (i.eval ρ) (j.eval ρ) (f.eval ρ) := by
  simp only [it_map_m, It_map_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

def It_comp_d (f g h : M.Domain) : Prop := (∀ p, M.mem p h → ∃ x y, KPair_d M p x y) ∧
  ∀ x z, Rd_entry_d x z h ↔ ∃ y, Rd_entry_d x y f ∧ Rd_entry_d y z g
def it_comp_m {d} (f g h : Term d) : Formula 1 d := .conj
  (Formula.isRelation kpair_convention_l h) (Formula.isComposition kpair_convention_l h g f)
derive_free_closed it_comp_m

theorem it_comp_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (f g h : Term d) :
    Formula.satisfies ρ (it_comp_m f g h) ↔ It_comp_d (f.eval ρ) (g.eval ρ) (h.eval ρ) := by
  simp only [it_comp_m, It_comp_d, Formula.isComposition, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff (kp_pair_l hKP), Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),
    Definitional.Term.eval_weaken]; rfl

theorem It_comp_d.unique_l (hE : Extensional M) {f g h k : M.Domain} (hh : It_comp_d f g h) (hk : It_comp_d f g k) : h = k := by
  have sub a b (ha : It_comp_d f g a) (hb : It_comp_d f g b) p (hp : M.mem p a) : M.mem p b := by
    obtain ⟨x, y, hxy⟩ := ha.1 p hp
    obtain ⟨q, hq, hqb⟩ := (hb.2 x y).mpr ((ha.2 x y).mp ⟨p, hxy, hp⟩)
    exact kpair_unique_l M hE hq hxy ▸ hqb
  exact hE.eq_of_same_members h k fun p => ⟨sub h k hh hk p, sub k h hk hh p⟩

structure It_diagram_d (hZF : M.Models ZF) (ω α T Q G : M.Domain) : Prop where
  order : It_order_d α T
  model_function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) Q
  model_domain : M.IsDomainOf (kp_pair_l (ZF.modelsKP hZF)) α Q
  models : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R
  map_function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) G
  map_domain : M.IsDomainOf (kp_pair_l (ZF.modelsKP hZF)) T G
  elementary : ∀ i j f c X R d Y S, It_map_d G i j f → Rd_entry_d i c Q → Rd_entry_d j d Q →
    Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R → Smdl_d (kp_pair_l (ZF.modelsKP hZF)) d Y S →
    Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y f
  identity : ∀ i f, It_map_d G i i f → ∀ x y, Rd_entry_d x y f → x = y
  comp : ∀ i j k f g h, It_map_d G i j f → It_map_d G j k g → It_map_d G i k h →
    ∀ x y z, Rd_entry_d x y f → Rd_entry_d y z g → Rd_entry_d x z h

variable (hZF : M.Models ZF) {ω α T Q G : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_diagram_d.model_l (h : It_diagram_d hZF ω α T Q G) {i : M.Domain} (hi : M.mem i α) :
    ∃ c X R, Rd_entry_d i c Q ∧ Smdl_d I c X R := by
  obtain ⟨c, hc⟩ := (h.model_domain i).mp hi
  obtain ⟨X, R, hm⟩ := h.models i c hc
  exact ⟨c, X, R, hc, hm⟩

theorem It_diagram_d.map_bound_l (h : It_diagram_d hZF ω α T Q G) {i j f : M.Domain}
    (hf : It_map_d G i j f) : Rd_entry_d i j T := by
  obtain ⟨r, hr, hrf⟩ := hf
  exact ⟨r, hr, (h.map_domain r).mpr ⟨f, hrf⟩⟩

theorem It_diagram_d.map_l (h : It_diagram_d hZF ω α T Q G) {i j : M.Domain} (hij : Rd_entry_d i j T) :
    ∃ f, It_map_d G i j f := by
  obtain ⟨r, hr, hrt⟩ := hij
  obtain ⟨f, hrf⟩ := (h.map_domain r).mp hrt
  exact ⟨f, r, hr, hrf⟩

theorem It_diagram_d.map_unique_l (h : It_diagram_d hZF ω α T Q G) {i j f g : M.Domain}
    (hf : It_map_d G i j f) (hg : It_map_d G i j g) : f = g := by
  obtain ⟨r, hr, hrf⟩ := hf
  obtain ⟨s, hs, hsg⟩ := hg
  exact h.map_function.2 r f g hrf ((kpair_unique_l M hZF.1 hs hr) ▸ hsg)

theorem it_comp_elementary_l {c d e X Y Z f g : M.Domain}
    (hf : Smap_d I ω c d X Y f) (hg : Smap_d I ω d e Y Z g) :
    ∃ h, Smap_d I ω c e X Z h ∧ It_comp_d f g h := by
  obtain ⟨h, hh, hs⟩ := smap_comp_l I hZF hf hg
  exact ⟨h, hh, hh.1.1.1.1, fun x z => (hs x z).trans
    ⟨And.right, fun ⟨y, hxy, hyz⟩ => ⟨hf.1.1.input_mem_of_pairMember hxy, y, hxy, hyz⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
