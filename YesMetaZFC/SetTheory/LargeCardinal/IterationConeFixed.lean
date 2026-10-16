import YesMetaZFC.SetTheory.LargeCardinal.IterationProjection
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFixed
import YesMetaZFC.SetTheory.MembershipInduction

/-! # 共尾多个根图的固定性传到良基极限

极限中的成员先由锥的覆盖性拉回某一阶段，再推进到固定低层的较晚阶段。
内部成员归纳于是证明根腿逐点固定该传递低层。这里不要求整个低层的像
等于低层，也不把极限固定性作为输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_cone_d.fixed_l {ω α T Q G b o c X R d N W P K : M.Domain}
    (hw : M.IsOmega ω) (diagram : It_diagram_d hZF ω α T Q G) (branch : It_branch_d α T b)
    (root : Rd_entry_d o c Q) (mx : Smem_d I c X R) (xt : M.TransitiveSet X)
    (mn : Smem_d I d N W) (nt : M.TransitiveSet N) (cone : It_cone_d hZF ω b Q G d N W P)
    (models : ∀ i a, Rd_entry_d i a Q → ∃ Y S, Smem_d I a Y S ∧ M.TransitiveSet Y)
    (kt : M.TransitiveSet K)
    (anchors : ∀ i, M.mem i b → ∃ k f, M.mem k b ∧ Rd_entry_d i k T ∧
      It_map_d G o k f ∧ ∀ x, M.mem x K → Rd_entry_d x x f) :
    ∀ r, Rd_entry_d o r P → ∀ x, M.mem x K → Rd_entry_d x x r := by
  have low : M.MemberSubset K X := by
    obtain ⟨i, hi, _⟩ := branch.cofinal o ((diagram.model_domain o).mpr ⟨c, root⟩)
    obtain ⟨k, f, hk, _, edge, fixed⟩ := anchors i hi
    obtain ⟨a, ha⟩ := (diagram.model_domain k).mp (branch.subset k hk)
    obtain ⟨Y, S, my, _⟩ := models k a ha
    exact fun x hx => (diagram.elementary o k f c X R a Y S edge root ha mx.1 my.1).1.1.input_mem_of_pairMember (fixed x hx)
  let ρ : Env M 3 := ⟨Fin.cases K (Fin.cases o (fun _ => P)), fun _ => K⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪⌜(.newest : Term 4)⌝ₛ ∈ ⌜(.bound 1 : Term 4)⌝ₛ →
    ∀ r y, ⌜rd_entry0_m⌝ₚ(⌜(.bound 2 : Term 4)⌝ₛ,r,⌜(.bound 3 : Term 4)⌝ₛ) →
      ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,y,r) → y = ⌜(.newest : Term 4)⌝ₛ⟫ }
  have sat x : φ.denote ρ x ↔ M.mem x K → ∀ r y, Rd_entry_d o r P → Rd_entry_d x y r → y = x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have fixed x (hx : M.mem x K) r y (hr : Rd_entry_d o r P) (xy : Rd_entry_d x y r) : y = x := by
    apply (sat x).mp (ZF.mem_ind_l M hZF I φ ρ ?_ x) hx r y hr xy
    intro x ih
    apply (sat x).mpr
    intro hx r y hr xy
    have jr := cone.elementary o r c X R hr root mx.1
    apply hZF.1.eq_of_same_members y x
    intro z
    constructor
    · intro zy
      obtain ⟨i, u, a, hi, az⟩ := cone.cover z (nt y (jr.1.1.output_mem_of_pairMember xy) z zy)
      obtain ⟨k, f, hk, ik, of, fk⟩ := anchors i ((cone.domain i).mpr ⟨u, hi⟩)
      obtain ⟨e, he⟩ := (diagram.model_domain i).mp (branch.subset i ((cone.domain i).mpr ⟨u, hi⟩))
      obtain ⟨c', hc⟩ := (diagram.model_domain k).mp (branch.subset k hk)
      obtain ⟨Y, S, my, _⟩ := models i e he
      obtain ⟨Z, V, mz, _⟩ := models k c' hc
      obtain ⟨v, hv⟩ := (cone.domain k).mp hk
      obtain ⟨g, hg⟩ := diagram.map_l hZF ik
      have jg := diagram.elementary i k g e Y S c' Z V hg he hc my.1 mz.1
      have jv := cone.elementary k v c' Z V hv hc mz.1
      obtain ⟨a', _, aa⟩ := jg.1.1.2.2 a ((cone.elementary i u e Y S hi he my.1).1.1.input_mem_of_pairMember az)
      obtain ⟨z', _, az'⟩ := jv.1.1.2.2 a' (jg.1.1.output_mem_of_pairMember aa)
      have eq := (cone.elementary i u e Y S hi he my.1).1.1.1.2 a z' z
        (cone.commute i k g u v hg hi hv a a' z' aa az') az
      have az : Rd_entry_d a' z v := eq ▸ az'
      obtain ⟨y', _, xy'⟩ := jv.1.1.2.2 x
        ((diagram.elementary o k f c X R c' Z V of root hc mx.1 mz.1).1.1.output_mem_of_pairMember (fk x hx))
      have ey := jr.1.1.1.2 x y' y (cone.commute o k f r v of hr hv x x y' (fk x hx) xy') xy
      have ax := (jv.member_l I hZF hw mz mn az (ey ▸ xy')).mpr zy
      have rootz := cone.commute o k f r v of hr hv a' a' z (fk a' (kt x hx a' ax)) az
      exact ((sat a').mp (ih a' ax) (kt x hx a' ax) r z hr rootz).symm ▸ ax
    · intro zx
      obtain ⟨z', _, zz⟩ := jr.1.1.2.2 z (xt x (low x hx) z zx)
      have eq := (sat z).mp (ih z zx) (kt x hx z zx) r z' hr zz
      exact (jr.member_l I hZF hw mx mn (eq ▸ zz) xy).mp zx
  intro r hr x hx
  obtain ⟨y, _, xy⟩ := (cone.elementary o r c X R hr root mx.1).1.1.2.2 x (low x hx)
  exact fixed x hx r y hr xy ▸ xy

end YesMetaZFC.SetTheory.LargeCardinal
