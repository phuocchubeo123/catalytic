import Mathlib.Data.Int.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

inductive ThreeReg where
  | R1 | R2 | R3
  deriving DecidableEq, Repr

abbrev Val := Int

structure State where
  r1 : Val
  r2 : Val
  r3 : Val
  deriving Repr

def State.read (s : State) (r : ThreeReg) : Val :=
  match r with
  | .R1 => s.r1
  | .R2 => s.r2
  | .R3 => s.r3

def State.write (s : State) (r : ThreeReg) (v : Val) : State :=
  match r with
  | .R1 => { s with r1 := v }
  | .R2 => { s with r2 := v }
  | .R3 => { s with r3 := v }

@[ext] lemma State.ext (s t : State) :
  s.r1 = t.r1 → s.r2 = t.r2 → s.r3 = t.r3 → s = t := by
  cases s
  cases t
  intro h1 h2 h3
  cases h1
  cases h2
  cases h3
  rfl

@[ext] lemma State.ext_read (s t : State) :
  (∀ r : ThreeReg, s.read r = t.read r) → s = t := by
  intro h
  -- unfold both states and use the three registers
  cases s with
  | mk s1 s2 s3 =>
    cases t with
    | mk t1 t2 t3 =>
      have h1 := h ThreeReg.R1
      have h2 := h ThreeReg.R2
      have h3 := h ThreeReg.R3
      -- h1 : s1 = t1, etc.
      cases h1
      cases h2
      cases h3
      rfl

@[simp] lemma read_write_same (s : State) (r : ThreeReg) (v : Val) :
  (State.write s r v).read r = v := by
  cases r <;> cases s <;> simp [State.write, State.read]

-- Writing to a register preserves the other registers
@[simp] lemma read_write_ne (s : State) {r r' : ThreeReg} (v : Val) (h : r' ≠ r) :
  (State.write s r v).read r' = s.read r' := by
  cases r <;> cases r' <;> cases s <;> simp [State.write, State.read] at *

/-- Rename the registers of a state by σ. -/
def State.perm (σ : ThreeReg ≃ ThreeReg) (s : State) : State :=
  { r1 := s.read (σ.symm ThreeReg.R1)
    r2 := s.read (σ.symm ThreeReg.R2)
    r3 := s.read (σ.symm ThreeReg.R3) }

@[simp] lemma read_perm (σ : ThreeReg ≃ ThreeReg) (s : State) (r : ThreeReg) :
  (State.perm σ s).read r = s.read (σ.symm r) := by
  cases r <;> rfl

@[simp] lemma read_perm_apply
  (σ : ThreeReg ≃ ThreeReg) (s : State) (r : ThreeReg) :
  (State.perm σ s).read (σ r) = s.read r := by
  -- Start with read_perm specialized at σ r
  have := read_perm σ s (σ r)
  -- This states: (State.perm σ s).read (σ r) = s.read (σ.symm (σ r))
  -- Now rewrite σ.symm (σ r) to r
  simp [Equiv.symm_apply_apply]

lemma symm_eq_iff (σ : ThreeReg ≃ ThreeReg) (r r' : ThreeReg) :
  σ.symm r' = r ↔ r' = σ r := by
  constructor
  · intro h
    -- apply σ to both sides
    have := congrArg σ h
    -- σ (σ.symm r') = σ r → r' = σ r
    simpa [Equiv.apply_symm_apply] using this
  · intro h
    -- apply σ.symm to both sides
    have := congrArg σ.symm h
    -- σ.symm r' = σ.symm (σ r) = r
    simpa [Equiv.symm_apply_apply] using this

@[simp] lemma write_perm (σ : ThreeReg ≃ ThreeReg) (s : State) (r : ThreeReg) (v : Val) :
  State.perm σ (State.write s r v)
    = State.write (State.perm σ s) (σ r) v := by
  apply State.ext_read
  intro r'
  -- compare `read r'` on both sides
  -- Left:
  --   (State.perm σ (State.write s r v)).read r'
  -- = (State.write s r v).read (σ.symm r')        by read_perm
  -- Right:
  --   (State.write (State.perm σ s) (σ r) v).read r'
  --   is either v (if r' = σ r) or the old value.
  have h_eq : σ.symm r' = r ∨ σ.symm r' ≠ r := by
    by_cases h : σ.symm r' = r
    · exact Or.inl h
    · exact Or.inr h
  rcases h_eq with h | h
  · -- case σ.symm r' = r  ⇔ r' = σ r
    have hr' : r' = σ r := (symm_eq_iff σ r r').1 h
    -- LHS:
    simp [read_perm, h, read_write_same]   -- (σ.symm r' = r) ⇒ read gives v
    -- RHS:
    simp [hr', read_write_same]
  · -- case σ.symm r' ≠ r  ⇔ r' ≠ σ r
    have hr' : r' ≠ σ r := by
      -- contrapositive: r' = σ r ⇒ σ.symm r' = r
      intro hr'
      apply h
      exact (symm_eq_iff σ r r').2 hr'
    -- LHS:
    simp [read_perm, read_write_ne, h]
    -- RHS:
    simp [read_write_ne, hr']

/- Define the property of 3 distinct registers and its permutation -/
def distinct3 (i j k : ThreeReg) : Prop :=
  i ≠ j ∧ j ≠ k ∧ k ≠ i

lemma distinct3_map (σ : ThreeReg ≃ ThreeReg) {i j k} (h : distinct3 i j k) :
  distinct3 (σ i) (σ j) (σ k) := by
  rcases h with ⟨hij, hjk, hki⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hij'
    apply hij
    exact σ.injective hij'
  · intro hjk'
    apply hjk
    exact σ.injective hjk'
  · intro hki'
    apply hki
    exact σ.injective hki'

/- Now start defining instructions-/
inductive Instr where
  | load (x : Val) (dst : ThreeReg)
  | load_rev (x : Val) (dst : ThreeReg)
  | add_const (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | add_const_rev (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | add_reg (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  | add_reg_rev (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  | mul_const (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | mul_const_rev (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | mul_reg (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  | mul_reg_rev (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  deriving Repr

def Instr.perm (σ : ThreeReg ≃ ThreeReg) : Instr → Instr
  | .load x dst         => .load x (σ dst)
  | .load_rev x dst     => .load_rev x (σ dst)
  | .add_const src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .add_const (σ src) x (σ dst) h'
  | .add_const_rev src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .add_const_rev (σ src) x (σ dst) h'
  | .add_reg src1 src2 dst h =>
      .add_reg (σ src1) (σ src2) (σ dst) (distinct3_map σ h)
  | .add_reg_rev src1 src2 dst h =>
      .add_reg_rev (σ src1) (σ src2) (σ dst) (distinct3_map σ h)
  | .mul_const src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .mul_const (σ src) x (σ dst) h'
  | .mul_const_rev src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .mul_const_rev (σ src) x (σ dst) h'
  | .mul_reg src1 src2 dst h =>
      .mul_reg (σ src1) (σ src2) (σ dst) (distinct3_map σ h)
  | .mul_reg_rev src1 src2 dst h =>
      .mul_reg_rev (σ src1) (σ src2) (σ dst) (distinct3_map σ h)

-- Defining big step semantics for Instructions
def Instr.exec (i : Instr) (s : State) : State :=
  match i with
  | .load x dst =>
    let v := s.read dst + x
    s.write dst v
  | .load_rev x dst =>
    let v := s.read dst - x
    s.write dst v
  | .add_const src x dst _ =>
    let v := s.read dst + s.read src + x
    s.write dst v
  | .add_const_rev src x dst _ =>
    let v := s.read dst - (s.read src + x)
    s.write dst v
  | .add_reg src1 src2 dst _ =>
    let v := s.read dst + s.read src1 + s.read src2
    s.write dst v
  | .add_reg_rev src1 src2 dst _ =>
    let v := s.read dst - (s.read src1 + s.read src2)
    s.write dst v
  | .mul_const src x dst _ =>
    let v := s.read dst + x * s.read src
    s.write dst v
  | .mul_const_rev src x dst _ =>
    let v := s.read dst - x * s.read src
    s.write dst v
  | .mul_reg src1 src2 dst _ =>
    let v := s.read dst + s.read src1 * s.read src2
    s.write dst v
  | .mul_reg_rev src1 src2 dst _ =>
   let v := s.read dst - s.read src1 * s.read src2
   s.write dst v

lemma instr_exec_perm (σ : ThreeReg ≃ ThreeReg) (i : Instr) (s : State) :
  Instr.exec (Instr.perm σ i) (State.perm σ s)
    = State.perm σ (Instr.exec i s) := by
  cases i with
  | load x dst =>
      -- LHS: write (σ dst) ((State.perm σ s).read (σ dst) + x)
      -- RHS: perm (write dst (s.read dst + x))
      -- use read_perm_apply to identify the value, then write_perm
      simp [Instr.exec, Instr.perm, write_perm]
  | load_rev x dst =>
      simp [Instr.exec, Instr.perm, write_perm]
  | add_const src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm]
  | add_const_rev src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_assoc, add_comm]
  | add_reg src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm, add_left_comm]
  | add_reg_rev src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_assoc, add_comm]
  | mul_const src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm]
  | mul_const_rev src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_comm]
  | mul_reg src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm]
  | mul_reg_rev src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_comm]

/- Define the reverse for instructions-/
def Instr.rev : Instr → Instr
  | Instr.load x dst =>
      Instr.load_rev x dst

  | Instr.load_rev x dst =>
      Instr.load x dst


  | Instr.add_const src x dst h =>
      Instr.add_const_rev src x dst h

  | Instr.add_const_rev src x dst h =>
      Instr.add_const src x dst h


  | Instr.add_reg src1 src2 dst h =>
      Instr.add_reg_rev src1 src2 dst h

  | Instr.add_reg_rev src1 src2 dst h =>
      Instr.add_reg src1 src2 dst h


  | Instr.mul_const src x dst h =>
      Instr.mul_const_rev src x dst h

  | Instr.mul_const_rev src x dst h =>
      Instr.mul_const src x dst h


  | Instr.mul_reg src1 src2 dst h =>
      Instr.mul_reg_rev src1 src2 dst h

  | Instr.mul_reg_rev src1 src2 dst h =>
      Instr.mul_reg src1 src2 dst h

@[simp] lemma sub_add_add_cancel_val (a b c : Val) :
  a - (b + c) + b + c = a := by
  ring

@[simp] lemma exec_add_const
    (src dst : ThreeReg) (h : src ≠ dst) (k : Val) (s : State) :
  Instr.exec (Instr.add_const src k dst h) s =
    State.write s dst (s.read dst + (s.read src + k)) := by
    simp [Instr.exec, add_assoc]

@[simp] lemma exec_add_const_rev
    (src dst : ThreeReg) (h : src ≠ dst) (k : Val) (s : State) :
  Instr.exec (Instr.add_const_rev src k dst h) s =
    State.write s dst (s.read dst - (s.read src + k)) := rfl

lemma instr_rev (i : Instr) (s : State) :
  Instr.exec (Instr.rev i) (Instr.exec i s) = s := by
  apply State.ext_read
  intro r
  cases i with
  | load x dst =>
    by_cases hrd : r = dst
    · subst hrd
      simp [Instr.exec, Instr.rev, read_write_same, sub_eq_add_neg,
              add_comm, add_left_comm]
    ·
      simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd, sub_eq_add_neg]
  | load_rev x dst =>
    by_cases hrd : r = dst
    · subst hrd
      simp [Instr.exec, Instr.rev, read_write_same, sub_eq_add_neg,
              add_comm]
    ·
      simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd, sub_eq_add_neg]
  | add_const src x dst h =>
      -- v1 = s.read dst + s.read src + x
      -- v2 = v1 - (s.read src + x) = s.read dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  | add_const_rev src x dst h =>
      -- first subtract, then add back
      -- v1 = s.read dst - (s.read src + x)
      -- v2 = v1 + s.read src + x = s.read dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_left_comm]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  | add_reg src1 src2 dst h =>
      -- v1 = dst + src1 + src2
      -- v2 = v1 - (src1 + src2) = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev,
              read_write_same,
              read_write_ne, h_src1_ne_dst, h_src2_ne_dst,
              sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc]
      ·
        simp [Instr.exec, Instr.rev, read_write_same, hrd]
  | add_reg_rev src1 src2 dst h =>
      -- v1 = dst - (src1 + src2)
      -- v2 = v1 + src1 + src2 = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev, read_write_same,
              h_src1_ne_dst, h_src2_ne_dst,
              sub_eq_add_neg, add_comm, add_left_comm]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd,
              sub_eq_add_neg, add_comm, add_assoc]
  | mul_const src x dst h =>
      -- v1 = dst + x * src
      -- v2 = v1 - x * src = dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_assoc]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm, add_left_comm]
  | mul_const_rev src x dst h =>
      -- v1 = dst - x * src
      -- v2 = v1 + x * src = dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_left_comm]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm]
  | mul_reg src1 src2 dst h =>
      -- v1 = dst + src1 * src2
      -- v2 = v1 - src1 * src2 = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne,
              h_src1_ne_dst, h_src2_ne_dst,
              sub_eq_add_neg, add_comm, add_assoc]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd,
              sub_eq_add_neg, add_comm, add_assoc]
  | mul_reg_rev src1 src2 dst h =>
      -- v1 = dst - src1 * src2
      -- v2 = v1 + src1 * src2 = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne,
              sub_eq_add_neg, add_comm, add_left_comm,
              h_src1_ne_dst, h_src2_ne_dst]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd,
              sub_eq_add_neg, add_comm, add_assoc]

@[simp] lemma instr_rev_rev (i : Instr) : i.rev.rev = i := by
  cases i <;> rfl

lemma instr_rev2 (i : Instr) (s : State) :
  Instr.exec i (Instr.exec (Instr.rev i) s) = s := by
  -- use `instr_rev` on `i.rev`
  simpa [instr_rev_rev] using instr_rev (i := i.rev) (s := s)

/- Now we can define program, and permutations-/
abbrev Program := List Instr

def Program.perm (σ : ThreeReg ≃ ThreeReg) (p : Program) : Program :=
  p.map (Instr.perm σ)

def Program.exec : Program → State → State
  | [], s => s
  | i :: p, s => Program.exec p (Instr.exec i s)

def Program.rev : Program → Program
  | []      => []
  | i :: p  => Program.rev p ++ ([i.rev] : Program)

lemma exec_append (p q : Program) (s : State) :
  Program.exec (p ++ q) s = Program.exec q (Program.exec p s) := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec]
  | cons i p ih =>
      simp [Program.exec, List.cons_append, ih]

@[simp]
lemma exec_singleton (i : Instr) (s : State) :
  Program.exec [i] s = Instr.exec i s := by
  -- [i] = i :: []
  -- Program.exec (i :: []) s = Program.exec [] (Instr.exec i s)
  have := exec_append [i] [] s
  -- rewrite Program.exec [] u = u
  simp [Program.exec]

lemma exec_perm (σ : ThreeReg ≃ ThreeReg) (p : Program) (s : State) :
  Program.exec (Program.perm σ p) (State.perm σ s)
    = State.perm σ (Program.exec p s) := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec, Program.perm, State.perm]
  | cons i p ih =>
      have h' := ih (Instr.exec i s)
      simpa [Program.exec, Program.perm, instr_exec_perm] using h'

/- Proven that the reverse program is correct!-/
lemma exec_rev (p : Program) (s : State) :
  Program.exec (Program.rev p) (Program.exec p s) = s := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec, Program.rev]
  | cons i p ih =>
      -- p = i :: p
      simp [Program.exec, Program.rev, exec_append, ih, instr_rev]

lemma exec_rev2 (p : Program) (s : State) :
  Program.exec p (Program.exec (Program.rev p) s) = s := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec, Program.rev]
  | cons i p ih =>
      simp [Program.exec, Program.rev, exec_append, instr_rev2, ih]

/- Some desired properties that a program wants to have-/
-- “p adds a constant x to register r, while preserving other registers”
def writes_add (p : Program) (r : ThreeReg) (x : Val) : Prop :=
  ∀ s, Program.exec p s = State.write s r (s.read r + x)

/- If a program can writes_add, its inverse can write_add_rev-/
lemma writes_add_rev
  (p : Program)
  (r : ThreeReg)
  (x : Val)
  (h : writes_add p r x) :
  writes_add (Program.rev p) r (-x) := by
  intro t
  let s := Program.exec (Program.rev p) t
  have hs_def : s = Program.exec p.rev t := rfl
  -- 1. Use writes_add on s:
  have h_p_s : p.exec s = State.write s r (s.read r + x) := h s
  -- 2. Use reversibility: p (p.rev t) = t
  have h_rev : p.exec s = t := by
    -- exec_rev2 : Program.exec p (Program.exec (Program.rev p) s) = s
    simpa [s, hs_def] using (exec_rev2 p t)
  -- Combine them: t = write s r (s.read r + x)
  have ht : t = s.write r (s.read r + x) := by
    -- from h_p_s and h_rev
    simpa [h_rev,eq_comm] using h_p_s.symm

  apply State.ext_read
  intro r'
  by_cases hr' : r' = r
  · subst hr'
    -- First compute t.read r from ht
    have h_tr : t.read r' = s.read r' + x := by
      -- ht : t = write s r (s.read r + x)
      -- so t.read r = (write s r (s.read r + x)).read r = s.read r + x
      simp [ht, read_write_same]

    -- We want s.read r = t.read r - x
    have hs_eq : s.read r' = t.read r' - x := by
      -- simple Int algebra using h_tr
      calc
        s.read r'
            = s.read r' + x - x := by ring
        _   = (s.read r' + x) - x := by rfl
        _   = t.read r' - x := by
                simp [h_tr]  -- replace t.read r with s.read r + x

    -- RHS: (State.write t r (t.read r - x)).read r = t.read r - x
    -- so we just rewrite with hs_eq
    simpa [read_write_same, hs_eq]
  · -- Case r' ≠ r
    -- We need: s.read r' = (State.write t r (t.read r - x)).read r'
    -- From ht, t is "write-at-r" of s, so all other regs are preserved:
    have h_tr' : t.read r' = s.read r' := by
      -- t = write s r (s.read r + x), reading at r' ≠ r
      have : r' ≠ r := hr'
      simp [ht, read_write_ne _ _ this]  -- t.read r' = s.read r'

    -- And writing t at r preserves r' as well:
    have h_write_t : (State.write t r (t.read r - x)).read r' = t.read r' := by
      have : r' ≠ r := hr'
      simp [read_write_ne _ _ this]

    -- Combine:
    calc
      s.read r'
          = t.read r' := by simp [h_tr']
      _   = (State.write t r (t.read r - x)).read r' := by
              simp [h_write_t]


/- Define a half ADD gadget first-/
def halfADD
    (ri rk : ThreeReg) (P1 : Program) (hik : ri ≠ rk) : Program :=
  [Instr.add_const_rev ri 0 rk hik] ++
  P1 ++
  [Instr.add_const ri 0 rk hik] ++
  Program.rev P1

lemma halfADD_correct
  (ri rk : ThreeReg)
  (P1 : Program)
  (hik : ri ≠ rk)
  (x : Val)
  (hP1 : writes_add P1 ri x) :
  writes_add (halfADD ri rk P1 hik) rk x := by
  intro s
  -- states after each phase
  set s1 := Program.exec [Instr.add_const_rev ri 0 rk hik] s with hs1
  set s2 := Program.exec P1 s1 with hs2
  set s3 := Program.exec [Instr.add_const ri 0 rk hik] s2 with hs3
  set s4 := Program.exec (Program.rev P1) s3 with hs4
    -- identify full exec with s4
  have h_exec :
    Program.exec (halfADD ri rk P1 hik) s = s4 := by
    unfold halfADD
    -- Now goal is:
    -- Program.exec ([sub] ++ P1 ++ [add] ++ P1.rev) s = s4

    -- Step 1: peel off [sub]
    have h_step1 :
      Program.exec ([Instr.add_const_rev ri 0 rk hik] ++ P1 ++ [Instr.add_const ri 0 rk hik] ++ P1.rev) s
        = Program.exec (P1 ++ [Instr.add_const ri 0 rk hik] ++ P1.rev) s1 := by
        -- use exec_append with p = [sub], q = P1 ++ [add] ++ P1.rev
        have h := exec_append
          ([Instr.add_const_rev ri 0 rk hik] : Program)
          (P1 ++ [Instr.add_const ri 0 rk hik] ++ P1.rev)
          s
        -- h :
        --   Program.exec ([Instr.add_const_rev ...] ++ (P1 ++ [add] ++ P1.rev)) s
        --     = Program.exec (P1 ++ [add] ++ P1.rev) (Program.exec [Instr.add_const_rev ...] s)
        -- rewrite associativity and the definition of s1
        simpa [List.append_assoc, s1, hs1] using h

    -- Step 2: peel off P1
    have h_step2 :
      Program.exec (P1 ++ [Instr.add_const ri 0 rk hik] ++ P1.rev) s1
        = Program.exec ([Instr.add_const ri 0 rk hik] ++ P1.rev) s2 := by
        -- exec_append with p = P1, q = [add] ++ P1.rev, starting from s1
        have h := exec_append
          (P1 : Program)
          ([Instr.add_const ri 0 rk hik] ++ P1.rev)
          s1
        -- h :
        --   Program.exec (P1 ++ ([add] ++ P1.rev)) s1
        --     = Program.exec ([add] ++ P1.rev) (Program.exec P1 s1)
        simpa [List.append_assoc, s2, hs2] using h

    -- Step 3: peel off [add]
    have h_step3 :
      Program.exec ([Instr.add_const ri 0 rk hik] ++ P1.rev) s2
        = Program.exec P1.rev s3 := by
        -- exec_append with p = [add], q = P1.rev, starting from s2
        have h := exec_append
          ([Instr.add_const ri 0 rk hik] : Program)
          (P1.rev)
          s2
        -- h :
        --   Program.exec ([add] ++ P1.rev) s2
        --     = Program.exec P1.rev (Program.exec [add] s2)
        simpa [s3, hs3] using h

    -- Now chain the three steps and finally use hs4
    calc
      Program.exec ([Instr.add_const_rev ri 0 rk hik] ++ P1 ++ [Instr.add_const ri 0 rk hik] ++ P1.rev) s
          = Program.exec (P1 ++ [Instr.add_const ri 0 rk hik] ++ P1.rev) s1 := h_step1
      _   = Program.exec ([Instr.add_const ri 0 rk hik] ++ P1.rev) s2 := h_step2
      _   = Program.exec P1.rev s3 := h_step3
      _   = s4 := by simp [s4]

  -- 2. Now prove s4 = write s rk (s.read rk + x) by extensionality
  ------------------------------------------------------------------
    -- We want: s4 = State.write s rk (s.read rk + x)
  apply (h_exec.trans ?_)
  apply State.ext_read
  intro q
  by_cases hq_rk : q = rk
  ------------------------------------------------------------------
  -- CASE 1: q = rk  (the destination register)
  ------------------------------------------------------------------
  · subst hq_rk

    -- s1: rk := rk - ri
    have hrk_s1 :
      s1.read q = s.read q - (s.read ri + 0) := by
      -- use your lemma about add_const_rev with k=0
      simp [s1, exec_add_const_rev, read_write_same]

    have hri_s1 :
      s1.read ri = s.read ri := by
      -- add_const_rev only writes rk
      have : ri ≠ q := hik
      simp [s1, exec_add_const_rev, this, read_write_ne]

    -- s2: P1 on s1: ri := ri + x, rk unchanged
    have hP1_s1 :
      Program.exec P1 s1 = State.write s1 ri (s1.read ri + x) :=
      hP1 s1

    have hrk_s2 :
      s2.read q = s1.read q := by
      have : q ≠ ri := by simpa [ne_comm] using hik
      simp [s2, hP1_s1, read_write_ne _ _ this]

    have hri_s2 :
      s2.read ri = s1.read ri + x := by
      simp [s2, hP1_s1, read_write_same]

    -- s3: rk := rk + (ri + 0)
    have hrk_s3 :
      s3.read q = s2.read q + (s2.read ri + 0) := by
      simp [s3, exec_add_const, read_write_same]

    -- express s3.read rk in terms of the original s
    have hrk_s3' :
      s3.read q = s.read q + x := by
      calc
        s3.read q
            = s2.read q + (s2.read ri + 0) := hrk_s3
        _   = s1.read q + ((s1.read ri + x) + 0) := by
                simp [hrk_s2, hri_s2]
        _   = s.read q - (s.read ri + 0) + (s.read ri + x) := by
                simp [hrk_s1, hri_s1, add_comm, add_left_comm, add_assoc]
        _   = s.read q + x := by
                ring

    -- s4: P1.rev on s3; it changes ri, not rk
    have hP1_rev : writes_add (Program.rev P1) ri (-x) :=
      writes_add_rev P1 ri x hP1

    have hP1_rev_s3 :
      Program.exec (Program.rev P1) s3 =
        State.write s3 ri (s3.read ri - x) :=
      hP1_rev s3

    have hrk_s4 :
      s4.read q = s3.read q := by
      have : q ≠ ri := by simpa [ne_comm] using hik
      simp [s4, hP1_rev_s3, read_write_ne _ _ this]

    -- final rk
    have : s4.read q = s.read q + x := by
      simp [hrk_s4, hrk_s3']
    -- RHS: write s rk (s.read rk + x)
    simpa [read_write_same] using this

  ------------------------------------------------------------------
  -- CASE 2: q ≠ rk  (“other registers”)
  ------------------------------------------------------------------
  · have hq_ne_rk : q ≠ rk := hq_rk

    -- We have to treat q = ri and q ≠ ri separately!

    by_cases hq_ri : q = ri
    --------------------------------------------------------------
    -- 2a: q = ri
    --------------------------------------------------------------
    · subst hq_ri

      -- s1: sub step only touches rk, so ri unchanged
      have hri_s1 :
        s1.read q = s.read q := by
        have : q ≠ rk := hik
        simp [s1, exec_add_const_rev, this, read_write_ne]

      -- s2: P1 adds x to ri
      have hP1_s1 :
        Program.exec P1 s1 = State.write s1 q (s1.read q + x) :=
        hP1 s1

      have hri_s2 :
        s2.read q = s1.read q + x := by
        simp [s2, hP1_s1, read_write_same]

      -- s3: add step only touches rk, so ri unchanged
      have hri_s3 :
        s3.read q = s2.read q := by
        simp [s3, exec_add_const, read_write_ne _ _ hq_ne_rk]

      -- s4: P1.rev subtracts x from ri
      have hP1_rev : writes_add (Program.rev P1) q (-x) :=
        writes_add_rev P1 q x hP1
      have hP1_rev_s3 :
        Program.exec (Program.rev P1) s3 =
          State.write s3 q (s3.read q - x) :=
        hP1_rev s3

      have hri_s4 :
        s4.read q = s3.read q - x := by
        simp [s4, hP1_rev_s3, read_write_same]

      -- combine everything: net effect on ri is 0
      have : s4.read q = s.read q := by
        calc
          s4.read q
              = s3.read q - x := hri_s4
          _   = (s2.read q) - x := by simp [hri_s3]
          _   = (s1.read q + x) - x := by simp [hri_s2]
          _   = s1.read q := by ring
          _   = s.read q := by simp [hri_s1]

      -- RHS: write at rk preserves ri since ri ≠ rk
      have : s4.read q = (State.write s rk (s.read rk + x)).read q := by
        simp [this, read_write_ne _ _ hik]

      simpa using this

    --------------------------------------------------------------
    -- 2b: q ≠ ri and q ≠ rk
    --------------------------------------------------------------
    · have hq_ne_ri : q ≠ ri := hq_ri

      -- s1: only rk changes
      have h_s1 : s1.read q = s.read q := by
        simp [s1, exec_add_const_rev, read_write_ne _ _ hq_ne_rk]

      -- s2: P1 writes ri, q ≠ ri
      have hP1_s1 :
        Program.exec P1 s1 = State.write s1 ri (s1.read ri + x) :=
        hP1 s1

      have h_s2 : s2.read q = s1.read q := by
        simp [s2, hP1_s1, read_write_ne _ _ hq_ne_ri]

      -- s3: only rk changes
      have h_s3 : s3.read q = s2.read q := by
        simp [s3, exec_add_const, read_write_ne _ _ hq_ne_rk]

      -- s4: P1.rev writes ri, q ≠ ri
      have hP1_rev : writes_add (Program.rev P1) ri (-x) :=
        writes_add_rev P1 ri x hP1
      have hP1_rev_s3 :
        Program.exec (Program.rev P1) s3 =
          State.write s3 ri (s3.read ri - x) :=
        hP1_rev s3

      have h_s4 : s4.read q = s3.read q := by
        simp [s4, hP1_rev_s3, read_write_ne _ _ hq_ne_ri]

      -- chain: s4.read q = s.read q
      have : s4.read q = s.read q := by
        simp [h_s4, h_s3, h_s2, h_s1]

      -- RHS: write at rk preserves q since q ≠ rk
      have : s4.read q = (State.write s rk (s.read rk + x)).read q := by
        simp [this, read_write_ne _ _ hq_ne_rk]

      simpa using this



/- We can finally start defining ADD program-/
def ADD
  (ri rj rk : ThreeReg)
  (P1 P2 : Program)
  (h : distinct3 ri rj rk)
  : Program :=
  let hki : rk ≠ ri := h.2.2
  let hik : ri ≠ rk := by
    simpa [ne_comm] using hki
  let hjk : rj ≠ rk := h.2.1
  [Instr.add_const_rev ri 0 rk hik] ++ P1 ++ [Instr.add_const ri 0 rk hik] ++ P1.rev ++
  [Instr.add_const_rev rj 0 rk hjk] ++ P2 ++ [Instr.add_const rj 0 rk hjk] ++ P2.rev

/- We now try to prove that this synthesize is correct-/
lemma ADD_eq_two_halves
  (ri rj rk : ThreeReg)
  (P1 P2 : Program)
  (h : distinct3 ri rj rk) :
  let hki : rk ≠ ri := h.2.2
  let hik : ri ≠ rk := by simpa [ne_comm] using hki
  let hjk : rj ≠ rk := h.2.1
  ADD ri rj rk P1 P2 h
    = halfADD ri rk P1 hik ++ halfADD rj rk P2 hjk := by
  intros hki hik hjk
  -- unfold both and massage with append associativity
  unfold ADD halfADD
  -- left is [ri-sub] ++ P1 ++ [ri-add] ++ P1.rev ++ [rj-sub] ++ P2 ++ [rj-add] ++ P2.rev
  -- right is ([ri-sub] ++ P1 ++ [ri-add] ++ P1.rev) ++ ([rj-sub] ++ P2 ++ [rj-add] ++ P2.rev)
  -- These are equal by associativity of ++
  simp [List.append_assoc]

theorem ADD_correct
  (ri rj rk : ThreeReg)
  (P1 P2 : Program)
  (h : distinct3 ri rj rk)
  (x y : Val)
  (hP1 : writes_add P1 ri x)
  (hP2 : writes_add P2 rj y) :
  writes_add (ADD ri rj rk P1 P2 h) rk (x + y) := by
  rcases h with ⟨hij, hjk, hki⟩
  have hik : ri ≠ rk := by simpa [ne_comm] using hki
  have hjk' : rj ≠ rk := hjk

  -- half-ADD gadgets for ri and rj
  have hhalf1 := halfADD_correct ri rk P1 hik x hP1
  have hhalf2 := halfADD_correct rj rk P2 hjk' y hP2

  intro s

  -- First do the ri-half:
  set s1 := Program.exec (halfADD ri rk P1 hik) s with hs1
  have hs1_spec :
      s1 = State.write s rk (s.read rk + x) := by
    -- from hhalf1 spec
    simpa [s1, hs1] using hhalf1 s

  -- Now relate ADD to the two halves and peel via exec_append
  have hadd_eq :
      ADD ri rj rk P1 P2 ⟨hij, hjk, hki⟩
        = halfADD ri rk P1 hik ++ halfADD rj rk P2 hjk' := by
    -- reuse the lemma above, inline if you like
    have := ADD_eq_two_halves ri rj rk P1 P2 ⟨hij, hjk, hki⟩
    -- expand the `let`s
    simpa [hik, hjk'] using this

  have h_exec_add :
      Program.exec (ADD ri rj rk P1 P2 ⟨hij, hjk, hki⟩) s
        = Program.exec (halfADD rj rk P2 hjk') s1 := by
    -- exec (p ++ q) s = exec q (exec p s)
    have h := exec_append (halfADD ri rk P1 hik) (halfADD rj rk P2 hjk') s
    simpa [hadd_eq, s1, hs1] using h

  -- Apply the second halfADD on s1
  have h_half2_s1 :
      Program.exec (halfADD rj rk P2 hjk') s1
        = State.write s1 rk (s1.read rk + y) :=
    hhalf2 s1

  -- Compose them
  have h_exec_total :
      Program.exec (ADD ri rj rk P1 P2 ⟨hij, hjk, hki⟩) s
        = State.write s1 rk (s1.read rk + y) := by
    simpa [h_exec_add] using h_half2_s1

  -- We know s1.read rk = s.read rk + x
  have hrk_s1 : s1.read rk = s.read rk + x := by
    simp [hs1_spec, read_write_same]

  -- We want to show:
  --   Program.exec (ADD ...) s = State.write s rk (s.read rk + (x + y))
  -- we already have h_exec_total, so rewrite and prove equality of writes.
  apply (h_exec_total.trans ?_)
  apply State.ext_read
  intro q
  by_cases hq : q = rk
  · ----------------------------------------------------------------
    -- Case q = rk: compute final rk value
    ----------------------------------------------------------------
    subst hq
    -- LHS read rk:
    have hL :
        (State.write s1 q (s1.read q + y)).read q
          = s1.read q + y := by
      simp [read_write_same]
    have hL' :
        (State.write s1 q (s1.read q + y)).read q
          = s.read q + (x + y) := by
      -- plug in s1.read rk and reassociate
      simp [hrk_s1, add_assoc, add_comm, add_left_comm]
    -- RHS read rk:
    have hR :
        (State.write s q (s.read q + (x + y))).read q
          = s.read q + (x + y) := by
      simp [read_write_same]
    -- done
    simpa [hR] using hL'

  · ----------------------------------------------------------------
    -- Case q ≠ rk: both writes preserve q
    ----------------------------------------------------------------
    have hq_ne_rk : q ≠ rk := hq

    -- First, show s1.read q = s.read q, since s1 = write at rk on s
    have h_s1q : s1.read q = s.read q := by
      have : q ≠ rk := hq_ne_rk
      simp [hs1_spec, read_write_ne _ _ this]

    -- LHS: write at rk on s1 preserves q
    have hL :
        (State.write s1 rk (s1.read rk + y)).read q
          = s1.read q := by
      simp [read_write_ne _ _ hq_ne_rk]

    -- RHS: write at rk on s preserves q
    have hR :
        (State.write s rk (s.read rk + (x + y))).read q
          = s.read q := by
      simp [read_write_ne _ _ hq_ne_rk]

    -- Compare them via h_s1q
    have :
        (State.write s1 rk (s1.read rk + y)).read q
          = (State.write s rk (s.read rk + (x + y))).read q := by
      simp [hL, hR, h_s1q]

    simpa using this
