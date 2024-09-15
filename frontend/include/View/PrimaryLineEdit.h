#ifndef PRIMARYLINEEDIT_H
#define PRIMARYLINEEDIT_H

#include <QLineEdit>

class PrimaryLineEdit : public QLineEdit
{
private:
    // Indicates whether the content of the line edit
    // is a result of a computation
    // or something the user has entered.
    bool containsResult_;

    // Sets the font from normal to bold (true) or vice versa (false).
    void setBold(bool enabled);

protected:
    // Reimplements QLineEdit::keyPressEvent.
    // In the case the user edits it with the keyboard
    // and it contains a result,
    // we would like the same to happen
    // as if they have pressed a button.
    virtual void keyPressEvent(QKeyEvent* event) override;

public:
    PrimaryLineEdit(QWidget*& parent);

    // This changes the content, if there was a result in it, to "Ans".
    virtual void mousePressEvent(QMouseEvent* e) override;
    // Returns whether this contains a result (so with bold text and special behaviour).
    bool containsResult() const;

public slots:
    // Concatenates a given text to the existing text.
    void addToText(const QString&);
    // Sets the line edit to the given test
    // but also sets the "containsResult" flag.
    void setResult(const QString&);
    // Sets the line edit to a base state
    // with no content and containsResult == false.
    void setBack();
};

#endif // PRIMARYLINEEDIT_H
