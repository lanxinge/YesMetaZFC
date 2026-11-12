import YesMetaZFC.SetTheory.Collapse.NaturalBasis
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 规范常零及后继图的有界读取与成员满保持

ω 已识别时，只须检查函数图及自然数坐标上的规范值；函数性给出完整图方程。
因此两张图随成员满嵌入保持，无须全初等性或相同实数集。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u v
variable {M : Structure.{u}}

def Mc_basis_d (ω z c s : M.Domain) : Prop :=
  (∀ y, ¬ M.mem y z) ∧ Fn0_d ω ω c ∧ Fn0_d ω ω s ∧
    (∀ i, M.mem i ω → Rd_entry_d i z c) ∧
      ∀ i y, M.mem i ω → M.mem y ω → M.SuccessorOf y i → Rd_entry_d i y s

def mc_basis_m {n} (ω z c s : Term n) : Formula 1 n := .conj (Formula.forallMem z .falsum) (set[n] ⟪
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜c⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜s⌝ₛ) ∧
  (∀ i ∈ ⌜ω⌝ₛ, ⌜rd_entry0_m⌝ₚ(i,⌜z⌝ₛ,⌜c⌝ₛ)) ∧
  (∀ i ∈ ⌜ω⌝ₛ, ∀ y ∈ ⌜ω⌝ₛ, ⌜KP.succ0_m⌝ₚ(y,i) → ⌜rd_entry0_m⌝ₚ(i,y,⌜s⌝ₛ))⟫)
derive_free_closed mc_basis_m

theorem mc_basis_delta_l {n} (ω z c s : Term n) : (mc_basis_m ω z c s).IsDelta0 :=
  .conj (.forallMem _ .falsum) (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..)
    (.conj (.forallMem _ (rd_entry0_delta_l ..)) (.forallMem _ (.forallMem _ (.imp (KP.succ0_delta_l ..) (rd_entry0_delta_l ..)))))))

theorem mc_basis_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω z c s : Term n) :
    Formula.satisfies ρ (mc_basis_m ω z c s) ↔ Mc_basis_d (ω.eval ρ) (z.eval ρ) (c.eval ρ) (s.eval ρ) := by
  simp only [mc_basis_m,Mc_basis_d,Formula.satisfies_conj_iff,Formula.satisfies_falsum_iff,fn0_sat_l hE,
    Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hE,KP.succ0_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e⟩ => ⟨a,b,c,d,fun i y hi hy => e i hi y hy⟩,
    fun ⟨a,b,c,d,e⟩ => ⟨a,b,c,d,fun i hi y hy => e i y hi hy⟩⟩

theorem mc_basis_iff_l (hE : Extensional M) {ω z c s : M.Domain} (hw : M.IsOmega ω) :
    Mc_basis_d ω z c s ↔ Mc_nat_d ω z c s := by
  constructor
  · rintro ⟨empty,fc,fs,zero,succ⟩
    refine ⟨hw,empty,fc,fun i y => ⟨?_,?_⟩,fs,fun i y => ⟨?_,?_⟩⟩
    · intro iy
      have hi := (fc.bound_l iy).1
      have iz := zero i hi
      exact ⟨hi,fc.2.2 i hi y (fc.bound_l iy).2 z (fc.bound_l iz).2 iy iz⟩
    · rintro ⟨hi,rfl⟩
      exact zero i hi
    · intro iy
      have hi := (fs.bound_l iy).1
      obtain ⟨y',sy,hy⟩ := hw.1.2 i hi
      have eq := fs.2.2 i hi y' hy y (fs.bound_l iy).2 (succ i y' hi hy sy) iy
      exact ⟨hi,eq ▸ sy⟩
    · rintro ⟨hi,sy⟩
      obtain ⟨y',sy',hy⟩ := hw.1.2 i hi
      exact succ i y hi (sy'.eq hE sy ▸ hy) sy
  · exact fun h => ⟨h.empty,h.constant,h.successor,fun i hi => (h.constant_entry i z).mpr ⟨hi,rfl⟩,
      fun i y hi _ sy => (h.successor_entry i y).mpr ⟨hi,sy⟩⟩

theorem Mc_nat_d.image_l {N : Structure.{v}} (hM : Extensional M) (hN : Extensional N)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {ω z c s : M.Domain} (basis : Mc_nat_d ω z c s) (hw : N.IsOmega (e ω)) :
    Mc_nat_d (e ω) (e z) (e c) (e s) := by
  let ρ : Env M 4 := ⟨fun i => [ω,z,c,s].get i,fun _ => ω⟩
  apply (mc_basis_iff_l hN hw).mp
  apply (mc_basis_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mp
  exact (delta0_image_l e inj full (mc_basis_delta_l ..) ρ).mp
    ((mc_basis_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mpr ((mc_basis_iff_l hM basis.omega).mpr basis))

end YesMetaZFC.SetTheory
